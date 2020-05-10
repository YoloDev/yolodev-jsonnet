use core::{
  hash::{BuildHasher, Hash, Hasher},
  mem,
  mem::MaybeUninit,
  num::NonZeroU32,
  pin::Pin,
  ptr,
  ptr::NonNull,
};
use hashbrown::{hash_map::RawEntryMut, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringId(NonZeroU32);

fn new_buf(cap: usize) -> Pin<Box<[MaybeUninit<u8>]>> {
  let buf = Box::new_uninit_slice(cap);
  buf.into()
}

#[inline]
unsafe fn str_comp(lhs: &str, rhs: &NonNull<str>) -> bool {
  let rhs: &str = rhs.as_ref();
  PartialEq::eq(lhs, rhs)
}

#[inline]
fn hash_str(mut hasher: impl Hasher, value: &str) -> u64 {
  value.hash(&mut hasher);
  hasher.finish()
}

pub struct StringInterner {
  map: HashMap<NonNull<str>, NonZeroU32>,
  vec: Vec<NonNull<str>>,
  buf: Pin<Box<[MaybeUninit<u8>]>>,
  pos: usize,
  full: Vec<Pin<Box<[MaybeUninit<u8>]>>>,
}

impl StringInterner {
  pub fn new() -> Self {
    Self::with_capacity(4096)
  }

  pub fn with_capacity(cap: usize) -> Self {
    let cap = cap.next_power_of_two();

    StringInterner {
      map: HashMap::default(),
      vec: Vec::new(),
      buf: new_buf(cap),
      pos: 0,
      full: Vec::new(),
    }
  }

  pub fn intern(&mut self, value: &str) -> StringId {
    let hash = hash_str(self.map.hasher().build_hasher(), value);
    let hasher = self.map.hasher().build_hasher();
    let id = match self
      .map
      .raw_entry_mut()
      .from_hash(hash, |other| unsafe { str_comp(value, other) })
    {
      RawEntryMut::Occupied(entry) => return StringId(*entry.get()),
      RawEntryMut::Vacant(entry) => {
        let key: NonNull<str> = {
          let cap = self.buf.len();
          if cap < self.pos + value.len() {
            let new_cap = (cap.max(value.len()) + 1).next_power_of_two();
            let new_buf = new_buf(new_cap);
            let old_buf = mem::replace(&mut self.buf, new_buf);
            self.pos = 0;
            self.full.push(old_buf);
          }

          let interned = {
            let pos = self.pos;
            let len = value.len();
            self.pos += len;

            unsafe {
              let buf = self.buf.as_mut().get_unchecked_mut();
              let start = MaybeUninit::first_ptr_mut(buf).offset(pos as isize);
              ptr::copy_nonoverlapping(value.as_bytes().as_ptr(), start, len);
              core::str::from_utf8_unchecked(core::slice::from_raw_parts(start, len))
            }
          };

          interned.into()
        };

        debug_assert_eq!(hash, {
          let key_ref = unsafe { key.as_ref() };
          hash_str(hasher, key_ref)
        });

        let index = self.vec.len();
        let id = unsafe { NonZeroU32::new_unchecked((index + 1) as u32) };
        entry.insert_hashed_nocheck(hash, key, id);
        self.vec.push(key);

        StringId(id)
      }
    };

    debug_assert_eq!(self.lookup(id), value);
    debug_assert_eq!(self.intern(value), id);

    id
  }

  pub fn lookup(&self, id: StringId) -> &str {
    let index = (id.0.get() - 1) as usize;
    unsafe { self.vec[index].as_ref() }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  mod string_id {
    use super::*;

    #[test]
    fn same_size_as_optional() {
      use std::mem;
      assert_eq!(
        mem::size_of::<StringId>(),
        mem::size_of::<Option<StringId>>()
      );
    }
  }

  #[test]
  fn simple() {
    StringInterner::new().intern("foo");
  }

  #[test]
  fn empty_string() {
    StringInterner::new().intern("");
  }

  #[test]
  fn same_twice() {
    let mut interner = StringInterner::new();
    let fst = interner.intern("foo");
    let snd = interner.intern("foo");
    assert_eq!(fst, snd);
  }

  #[test]
  fn two_different() {
    let mut interner = StringInterner::new();
    let fst = interner.intern("foo");
    let snd = interner.intern("bar");
    assert_ne!(fst, snd);
  }

  #[test]
  fn many() {
    let mut interner = StringInterner::with_capacity(8);
    let ids: Vec<_> = (0..100).map(|n| interner.intern(&n.to_string())).collect();
    for (index, id) in ids.into_iter().enumerate() {
      let string = interner.lookup(id);
      assert_eq!(string, &index.to_string(), "index: {}", index);
    }
  }
}
