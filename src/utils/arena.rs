use core::{
  hash::{Hash, Hasher},
  marker::PhantomData,
  mem,
  mem::MaybeUninit,
  num::NonZeroU32,
  ops::Index,
  pin::Pin,
  ptr,
  ptr::NonNull,
};

macro_rules! impl_id_traits {
  ($ty:ident, $dat:ty) => {
    impl<T: Sized> Clone for $ty<T> {
      #[inline]
      fn clone(&self) -> Self {
        *self
      }
    }

    impl<T: Sized> Copy for $ty<T> {}

    impl<T: Sized> PartialEq for $ty<T> {
      #[inline]
      fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self.0, &other.0)
      }

      #[inline]
      fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&self.0, &other.0)
      }
    }

    impl<T: Sized> Eq for $ty<T> {}

    impl<T: Sized> Hash for $ty<T> {
      #[inline]
      fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.0, state)
      }
    }

    impl<T: Sized> $ty<T> {
      #[inline]
      pub fn get(self, a: &Arena<T>) -> &$dat {
        &a[self]
      }
    }
  };
}

#[derive(Debug)]
pub(crate) struct Id<T: Sized>(NonZeroU32, PhantomData<*const T>);

impl_id_traits!(Id, T);

#[derive(Debug)]
pub(crate) struct SliceId<T: Sized>(NonZeroU32, PhantomData<*const [T]>);
impl_id_traits!(SliceId, [T]);

fn new_buf<T>(cap: usize) -> Pin<Box<[MaybeUninit<T>]>> {
  let buf = Box::new_uninit_slice(cap);
  buf.into()
}

unsafe fn drop_buf<T>(buf: &mut Pin<Box<[MaybeUninit<T>]>>, len: usize) {
  let buf = buf.as_mut().get_unchecked_mut();
  let mut ptr = MaybeUninit::first_ptr_mut(buf);
  for _ in 0..len {
    ptr::drop_in_place(ptr);
    ptr = ptr.add(1);
  }
}

pub(crate) struct Arena<T: Sized + 'static> {
  items: Vec<NonNull<T>>,
  slices: Vec<NonNull<[T]>>,
  buf: Pin<Box<[MaybeUninit<T>]>>,
  buf_len: usize,
  full: Vec<(Pin<Box<[MaybeUninit<T>]>>, usize)>,
}

impl<T: Sized + 'static> Drop for Arena<T> {
  fn drop(&mut self) {
    unsafe {
      drop_buf(&mut self.buf, self.buf_len);
      for (buf, buf_len) in &mut self.full {
        drop_buf(buf, *buf_len);
      }
    }
  }
}

impl<T: Sized + 'static> Arena<T> {
  pub fn new() -> Self {
    Self::with_capacity(0)
  }

  pub fn with_capacity(cap: usize) -> Self {
    if cap == 0 {
      return Arena {
        items: Vec::new(),
        slices: Vec::new(),
        buf: new_buf(0),
        buf_len: 0,
        full: Vec::new(),
      };
    }

    let cap = cap.next_power_of_two();

    Arena {
      items: Vec::new(),
      slices: Vec::new(),
      buf: new_buf(cap),
      buf_len: 0,
      full: Vec::new(),
    }
  }

  pub fn push(&mut self, item: T) -> Id<T> {
    let cap = self.buf.len();
    if cap < self.buf_len + 1 {
      let new_cap = (cap.max(3) + 1).next_power_of_two();
      let new_buf = new_buf(new_cap);
      let old_buf = mem::replace(&mut self.buf, new_buf);
      let old_len = self.buf_len;
      self.buf_len = 0;
      self.full.push((old_buf, old_len));
    }

    let pos = self.buf_len;
    self.buf_len += 1;

    let ptr = unsafe {
      let buf = self.buf.as_mut().get_unchecked_mut();
      let start = MaybeUninit::first_ptr_mut(buf).add(pos);
      start.write(item);
      NonNull::new_unchecked(start)
    };

    let index = self.items.len();
    let id = unsafe { NonZeroU32::new_unchecked((index + 1) as u32) };
    self.items.push(ptr);

    Id(id, PhantomData)
  }

  pub fn push_slice<I>(&mut self, items: I) -> SliceId<T>
  where
    I: IntoIterator<Item = T>,
    <I as IntoIterator>::IntoIter: ExactSizeIterator,
  {
    let items = items.into_iter();
    let items_len = items.len();
    if items_len == 0 {
      return self.empty_slice();
    }

    let cap = self.buf.len();
    if cap < self.buf_len + items_len {
      let new_cap = (cap.max(items_len) + 1).next_power_of_two();
      let new_buf = new_buf(new_cap);
      let old_buf = mem::replace(&mut self.buf, new_buf);
      let old_len = self.buf_len;
      self.buf_len = 0;
      self.full.push((old_buf, old_len));
    }

    let pos = self.buf_len;
    let start = unsafe {
      let buf = self.buf.as_mut().get_unchecked_mut();
      MaybeUninit::first_ptr_mut(buf).add(pos)
    };

    // This is to make sure that even if ExactSizeIterator
    // is badly implemented, we don't get more items than
    // we expect.
    let mut items = items.enumerate().take(items_len);
    let mut ptr = start;
    let mut len = 0;
    while let Some((idx, item)) = items.next() {
      len = idx + 1;
      unsafe {
        ptr.write(item);
        ptr = ptr.add(1);
      }
    }

    self.buf_len += len;
    let slice = unsafe {
      let slice = core::slice::from_raw_parts_mut(start, len);
      NonNull::new_unchecked(slice as *mut [T])
    };

    let index = self.slices.len();
    let id = unsafe { NonZeroU32::new_unchecked((index + 2) as u32) };
    self.slices.push(slice);

    SliceId(id, PhantomData)
  }

  pub fn empty_slice(&self) -> SliceId<T> {
    //SliceId(unsafe { NonZeroU32::new_unchecked(1) }, PhantomData)
    let id = unsafe { NonZeroU32::new_unchecked(1) };

    SliceId(id, PhantomData)
  }
}

impl<T: Sized> Index<Id<T>> for Arena<T> {
  type Output = T;

  #[inline]
  fn index(&self, id: Id<T>) -> &Self::Output {
    let index = (id.0.get() - 1) as usize;

    unsafe { self.items[index].as_ref() }
  }
}

impl<T: Sized> Index<SliceId<T>> for Arena<T> {
  type Output = [T];

  #[inline]
  fn index(&self, id: SliceId<T>) -> &Self::Output {
    let index = id.0.get();

    if index == 1 {
      &[]
    } else {
      let index = (index - 2) as usize;

      unsafe { self.slices[index].as_ref() }
    }
  }
}
