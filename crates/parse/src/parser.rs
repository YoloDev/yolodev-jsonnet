//! TODO: write short doc here

use core::cell::Cell;

use drop_bomb::DropBomb;

use crate::{
  event::Event,
  ParseError,
  SyntaxKind::{self, EOF, PARSE_ERR, TOMBSTONE},
  TokenSet, TokenSource,
};

/// `Parser` struct provides the low-level API for
/// navigating through the stream of tokens and
/// constructing the parse tree. The actual parsing
/// happens in the `grammar` module.
///
/// However, the result of this `Parser` is not a real
/// tree, but rather a flat stream of events of the form
/// "start expression, consume number literal,
/// finish expression". See `Event` docs for more.
pub(crate) struct Parser<'t, T: TokenSource> {
  token_source: &'t mut T,
  events: Vec<Event>,
  steps: Cell<u32>,
}

impl<'t, S: TokenSource> Parser<'t, S> {
  pub(super) fn new(token_source: &'t mut S) -> Self {
    Parser {
      token_source,
      events: Vec::new(),
      steps: Cell::new(0),
    }
  }

  pub(crate) fn finish(self) -> Vec<Event> {
    self.events
  }

  /// Returns the kind of the current token.
  /// If parser has already reached the end of input,
  /// the special `EOF` kind is returned.
  pub(crate) fn current(&self) -> SyntaxKind {
    self.nth(0)
  }

  /// Lookahead operation: returns the kind of the next nth
  /// token.
  pub(crate) fn nth(&self, n: usize) -> SyntaxKind {
    assert!(n <= 3);

    let steps = self.steps.get();
    assert!(steps <= 10_000_000, "the parser seems stuck");
    self.steps.set(steps + 1);

    self.token_source.lookahead_nth(n).kind
  }

  /// Checks if the current token is `kind`.
  /// Identical to `nth_at(0, kind)`.
  pub(crate) fn at(&self, kind: SyntaxKind) -> bool {
    self.nth_at(0, kind)
  }

  /// Checks if the nth token is `kind`.
  pub(crate) fn nth_at(&self, n: usize, kind: SyntaxKind) -> bool {
    self.token_source.lookahead_nth(n).kind == kind
  }

  /// Consume the next token if `kind` matches.
  pub(crate) fn eat(&mut self, kind: SyntaxKind) -> bool {
    if !self.at(kind) {
      return false;
    }

    self.do_bump(kind);
    true
  }

  /// Checks if the current token is in `kinds`.
  pub(crate) fn at_ts(&self, kinds: TokenSet) -> bool {
    kinds.contains(self.current())
  }

  /// Starts a new node in the syntax tree. All nodes and tokens
  /// consumed between the `start` and the corresponding `Marker::complete`
  /// belong to the same node.
  pub(crate) fn start(&mut self) -> Marker {
    let pos = self.events.len() as u32;
    self.push_event(Event::tombstone());
    Marker::new(pos)
  }

  /// Consume the next token if `kind` matches.
  pub(crate) fn bump(&mut self, kind: SyntaxKind) {
    assert!(self.eat(kind));
  }

  /// Advances the parser by one token
  pub(crate) fn bump_any(&mut self) {
    let kind = self.nth(0);
    if kind == EOF {
      return;
    }

    self.do_bump(kind)
  }

  /// Emit error with the `message`
  /// TODO: this should be much more fancy and support
  /// structured errors with spans and notes.
  pub(crate) fn error(&mut self, message: impl Into<String>) {
    let msg = ParseError(message.into());
    self.push_event(Event::Error { msg })
  }

  /// Consume the next token if it is `kind` or emit an error
  /// otherwise.
  pub(crate) fn expect(&mut self, kind: SyntaxKind) -> bool {
    if self.eat(kind) {
      return true;
    }

    self.error(format!("expected {:?}", kind));
    false
  }

  /// Create an error node and consume the next token.
  pub(crate) fn err_and_bump(&mut self, message: &str) {
    self.err_recover(message, TokenSet::EMPTY);
  }

  /// Create an error node and consume the next token.
  pub(crate) fn err_recover(&mut self, message: &str, recovery: TokenSet) {
    match self.current() {
      T!['{'] | T!['}'] => {
        self.error(message);
        return;
      }
      _ => (),
    }

    if self.at_ts(recovery) {
      self.error(message);
      return;
    }

    let m = self.start();
    self.error(message);
    self.bump_any();
    m.complete(self, PARSE_ERR);
  }

  fn do_bump(&mut self, kind: SyntaxKind) {
    self.token_source.bump();

    self.push_event(Event::Token { kind });
  }

  fn push_event(&mut self, event: Event) {
    self.events.push(event)
  }
}

/// See `Parser::start`.
pub(crate) struct Marker {
  pos: u32,
  bomb: DropBomb,
}

impl Marker {
  fn new(pos: u32) -> Marker {
    Marker {
      pos,
      bomb: DropBomb::new("Marker must be either completed or abandoned"),
    }
  }

  /// Finishes the syntax tree node and assigns `kind` to it,
  /// and mark the create a `CompletedMarker` for possible future
  /// operation like `.precede()` to deal with forward_parent.
  pub(crate) fn complete<S: TokenSource>(
    mut self,
    p: &mut Parser<S>,
    kind: SyntaxKind,
  ) -> CompletedMarker {
    self.bomb.defuse();
    let idx = self.pos as usize;
    match p.events[idx] {
      Event::Start {
        kind: ref mut slot, ..
      } => {
        *slot = kind;
      }
      _ => unreachable!(),
    }

    let finish_pos = p.events.len() as u32;
    p.push_event(Event::Finish);
    CompletedMarker::new(self.pos, finish_pos, kind)
  }

  /// Abandons the syntax tree node. All its children
  /// are attached to its parent instead.
  pub(crate) fn abandon<S: TokenSource>(mut self, p: &mut Parser<S>) {
    self.bomb.defuse();

    let idx = self.pos as usize;
    if idx == p.events.len() - 1 {
      match p.events.pop() {
        Some(Event::Start {
          kind: TOMBSTONE,
          forward_parent: None,
        }) => (),
        _ => unreachable!(),
      }
    }
  }
}

#[allow(dead_code)]
pub(crate) struct CompletedMarker {
  start_pos: u32,
  finish_pos: u32,
  kind: SyntaxKind,
}

impl CompletedMarker {
  fn new(start_pos: u32, finish_pos: u32, kind: SyntaxKind) -> Self {
    CompletedMarker {
      start_pos,
      finish_pos,
      kind,
    }
  }

  /// This method allows to create a new node which starts
  /// *before* the current one. That is, parser could start
  /// node `A`, then complete it, and then after parsing the
  /// whole `A`, decide that it should have started some node
  /// `B` before starting `A`. `precede` allows to do exactly
  /// that. See also docs about `forward_parent` in `Event::Start`.
  ///
  /// Given completed events `[START, FINISH]` and its corresponding
  /// `CompletedMarker(pos: 0, _)`.
  /// Append a new `START` events as `[START, FINISH, NEWSTART]`,
  /// then mark `NEWSTART` as `START`'s parent with saving its relative
  /// distance to `NEWSTART` into forward_parent(=2 in this case);
  pub(crate) fn precede<S: TokenSource>(self, p: &mut Parser<S>) -> Marker {
    let new_pos = p.start();
    let idx = self.start_pos as usize;

    match p.events[idx] {
      Event::Start {
        ref mut forward_parent,
        ..
      } => {
        *forward_parent = Some(new_pos.pos - self.start_pos);
      }
      _ => unreachable!(),
    }
    new_pos
  }

  /// Undo this completion and turns into a `Marker`
  pub(crate) fn undo_completion<S: TokenSource>(self, p: &mut Parser<S>) -> Marker {
    let start_idx = self.start_pos as usize;
    let finish_idx = self.finish_pos as usize;

    match p.events[start_idx] {
      Event::Start {
        ref mut kind,
        forward_parent: None,
      } => *kind = TOMBSTONE,
      _ => unreachable!(),
    }

    match p.events[finish_idx] {
      ref mut slot @ Event::Finish => *slot = Event::tombstone(),
      _ => unreachable!(),
    }

    Marker::new(self.start_pos)
  }

  // pub(crate) fn kind(&self) -> SyntaxKind {
  //   self.kind
  // }
}
