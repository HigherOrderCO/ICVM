// Implements Interaction Combinators. The Interaction Calculus is directly isomorphic to them, so,
// to reduce a term, we simply translate to interaction combinators, reduce, then translate back.

#![allow(dead_code)]

#[derive(Clone, Debug)]
pub struct INet {
  pub nodes: Vec<u32>,
  pub reuse: Vec<u32>,
  pub rewrite_count: u32,
}

pub type NodeKind = u32;

// Node types are consts because those are used in a Vec<u32>.
pub const TAG: NodeKind = 28;
pub const ERA: NodeKind = 0 << TAG;
pub const CON: NodeKind = 1 << TAG;
pub const ANN: NodeKind = 2 << TAG;
pub const DUP: NodeKind = 3 << TAG;
pub const FIX: NodeKind = 4 << TAG;
// pub const OBS: NodeKind = 5 << TAG;
pub const FUN: NodeKind = 6 << TAG;

pub const TAG_MASK: NodeKind = !((1 << TAG) - 1);

// The ROOT port is on the deadlocked root node at address 0.
pub const ROOT: u32 = 1;

// A port is just a u32 combining address (30 bits) and slot (2 bits).
pub type Port = u32;

// Create a new net, with a deadlocked root node.
pub fn new_inet() -> INet {
  INet {
    nodes: vec![2, 1, 0, 0], // p2 points to p0, p1 points to net
    reuse: vec![],
    rewrite_count: 0,
  }
}

// Allocates a new node, reclaiming a freed space if possible.
pub fn new_node(inet: &mut INet, kind: u32) -> u32 {
  let node: u32 = match inet.reuse.pop() {
    Some(index) => index,
    None => {
      let len = inet.nodes.len();
      inet.nodes.resize(len + 4, 0);
      (len as u32) / 4
    }
  };
  inet.nodes[port(node, 0) as usize] = port(node, 0);
  inet.nodes[port(node, 1) as usize] = port(node, 1);
  inet.nodes[port(node, 2) as usize] = port(node, 2);
  inet.nodes[port(node, 3) as usize] = kind;
  return node;
}

// Builds a port (an address / slot pair).
pub fn port(node: u32, slot: u32) -> Port {
  (node << 2) | slot
}

// Returns the address of a port (TODO: rename).
pub fn addr(port: Port) -> u32 {
  port >> 2
}

// Returns the slot of a port.
pub fn slot(port: Port) -> u32 {
  port & 3
}

// Enters a port, returning the port on the other side.
pub fn enter(inet: &INet, port: Port) -> Port {
  inet.nodes[port as usize]
}

// Enters a slot on the node pointed by this port.
pub fn get(inet: &INet, p: Port, s: u32) -> Port {
  enter(inet, port(addr(p), s))
}

// Kind of the node.
pub fn kind(inet: &INet, node: u32) -> u32 {
  inet.nodes[port(node, 3) as usize]
}

// Links two ports.
pub fn link(inet: &mut INet, ptr_a: u32, ptr_b: u32) {
  inet.nodes[ptr_a as usize] = ptr_b;
  inet.nodes[ptr_b as usize] = ptr_a;
}

// Reduces a wire to weak normal form.
pub fn reduce(inet: &mut INet, function_book: &FunctionBook, root: Port, skip: &dyn Fn(u32, u32) -> bool) {
  let mut path = vec![];
  let mut prev = root;
  loop {
    let next = enter(inet, prev);
    // If next is ROOT, stop.
    if next == ROOT {
      return;
    }
    // If next is a main port...
    if slot(next) == 0 {
      // Checks if caller asked to skip this rule.
      let skipped = skip(kind(inet, addr(prev)), kind(inet, addr(next)));
      // If prev is a main port, reduce the active pair.
      if slot(prev) == 0 && !skipped {
        inet.rewrite_count += 1;
        rewrite(inet, function_book, addr(prev), addr(next));

        if DEBUG.get().copied().unwrap_or_default() {
          let term = read_at(inet, ROOT, function_book);
          println!("R: {}", term);
        }

        prev = path.pop().unwrap();
        continue;
      // Otherwise, return the axiom.
      } else {
        return;
      }
    }
    // If next is an aux port, pass through.
    path.push(prev);
    prev = port(addr(next), 0);
  }
}

// Reduces the net to normal form.
pub fn normal(inet: &mut INet, function_book: &FunctionBook, root: Port) {
  let mut warp = vec![root];
  let mut tick = 0;
  while let Some(prev) = warp.pop() {
    reduce(inet, function_book, prev, &|ak, bk| false);
    let next = enter(inet, prev);
    if slot(next) == 0 {
      warp.push(port(addr(next), 1));
      warp.push(port(addr(next), 2));
    }

    if DEBUG.get().copied().unwrap_or_default() {
      let term = read_at(inet, ROOT, function_book);
      println!("N: {}", term);
    }
  }
}

/// Rewrites an active pair
pub fn rewrite(inet: &mut INet, function_book: &FunctionBook, x: Port, y: Port) {
  /// Insert the function body in place of the FUN node
  fn insert_function(
    inet: &mut INet,
    function_book: &FunctionBook,
    fun: Port,
    other: Port,
    fun_kind: NodeKind,
    other_kind: NodeKind,
  ) -> (u32, NodeKind) {
    let function_id = (fun_kind - FUN) as usize;
    let function_term = &function_book.function_id_to_terms[function_id].0;
    let host = port(other, 0);
    alloc_at(inet, function_term, host, function_book);

    inet.reuse.push(fun);

    let y = addr(enter(inet, host));
    let kind_x = other_kind;
    let kind_y = kind(inet, y);
    (y, kind_y)
  }

  let kind_x = kind(inet, x);
  let kind_y = kind(inet, y);

  // When one of the nodes is a FUN, replace it with the function net
  let ((x, kind_x), (y, kind_y)) = if kind_x & TAG_MASK == FUN {
    ((y, kind_y), insert_function(inet, function_book, x, y, kind_x, kind_y))
  } else if kind_y & TAG_MASK == FUN {
    ((x, kind_x), insert_function(inet, function_book, y, x, kind_y, kind_x))
  } else {
    ((x, kind_x), (y, kind_y))
  };

  if kind_x == kind_y {
    let p0 = enter(inet, port(x, 1));
    let p1 = enter(inet, port(y, 1));
    link(inet, p0, p1);
    let p0 = enter(inet, port(x, 2));
    let p1 = enter(inet, port(y, 2));
    link(inet, p0, p1);
    inet.reuse.push(x);
    inet.reuse.push(y);
  } else {
    let t = kind(inet, x);
    let a = new_node(inet, t);
    let t = kind(inet, y);
    let b = new_node(inet, t);
    let t = enter(inet, port(x, 1));
    link(inet, port(b, 0), t);
    let t = enter(inet, port(x, 2));
    link(inet, port(y, 0), t);
    let t = enter(inet, port(y, 1));
    link(inet, port(a, 0), t);
    let t = enter(inet, port(y, 2));
    link(inet, port(x, 0), t);
    link(inet, port(a, 1), port(b, 1));
    link(inet, port(a, 2), port(y, 1));
    link(inet, port(x, 1), port(b, 2));
    link(inet, port(x, 2), port(y, 2));
  }
}

// Composes two fixed points:
// @x(F x)     , @y(G y)
// -------------------------- fixpose
// @x(F (G x)) , @x(G (F x)))
// https://twitter.com/VictorTaelin/status/1659724812057452549
fn fixpose(inet: &mut INet, a: Port, b: Port) {
  if kind(inet, addr(a)) == FIX && kind(inet, addr(b)) == FIX && slot(a) == 2 && slot(b) == 2 {
    let ff = enter(inet, port(addr(a), 0));
    let fx = enter(inet, port(addr(a), 1));
    let gg = enter(inet, port(addr(b), 0));
    let gx = enter(inet, port(addr(b), 1));
    let fu = new_node(inet, FIX + 1);
    let fd = new_node(inet, FIX + 1);
    let gu = new_node(inet, FIX + 1);
    let gd = new_node(inet, FIX + 1);
    let up = new_node(inet, FIX + 1);
    let dw = new_node(inet, FIX + 1);
    let cc = new_node(inet, FIX);
    let rt = new_node(inet, FIX + 1);
    link(inet, port(fu, 0), ff);
    link(inet, port(fu, 1), port(gd, 2));
    link(inet, port(fu, 2), port(up, 1));
    link(inet, port(gu, 0), gg);
    link(inet, port(gu, 1), port(fd, 2));
    link(inet, port(gu, 2), port(up, 2));
    link(inet, port(fd, 0), fx);
    link(inet, port(fd, 1), port(dw, 2));
    link(inet, port(gd, 0), gx);
    link(inet, port(gd, 1), port(dw, 1));
    link(inet, port(cc, 0), port(up, 0));
    link(inet, port(cc, 1), port(dw, 0));
    link(inet, port(cc, 2), port(rt, 0));
    link(inet, port(rt, 1), enter(inet, a));
    link(inet, port(rt, 2), enter(inet, b));
  }
}

// Equality on Interaction Combinators
//
// A Path is a deque of aux slots (1 or 2)
//
// > type Slot = 1 | 2
// > type Path = [Slot]
//
// A cursor has a root port, a prev port, and a map of paths
//
// > type Cursor = { root: Port, prev: Port, path: Map<Kind, Path> }
//
// The equality function returns if two nets are equal
//
// > eq : INet -> Cursor -> Cursor -> Bool
//
// If we're on root, compare both deque maps
//
// > eq a am b bm = am == bm
//
// If main port, non-empty deque: pop_back a slot from this deque, and move to it
//
// > eq ak#[*a0 a1 a2] {[ak]:(1,ap),..am} b bm = eq a1 {[ak]:ap,..am} b bm
// > eq ak#[*a0 a1 a2] {[ak]:(2,ap),..am} b bm = eq a2 {[ak]:ap,..am} b bm
//
// If main port, empty deque: push_front [1,2] slots to the other deque, and move to both
//
// > eq ak#[*a0 a1 a2] {[ak]:ap,..am} b {[ak]:bs,..bm} = eq a1 ap b {[ak]:(bs,1),..bm}
//                                                     & eq a2 ap b {[ak]:(bs,2),..bm}
//
// If aux port, push_back it to this deque, and move to main port
//
// > eq ak[a0 *a1 a2] {[ak]:ap,..am} b bm = eq a1 {[ak]:(1,ap),..am} b bm
// > eq ak[a0 a1 *a2] {[ak]:ap,..am} b bm = eq a1 {[ak]:(2,ap),..am} b bm
//
// The rules above that match on 'a' are repeated for 'b'.

use crate::{
  term::{alloc_at, read_at, FunctionBook},
  DEBUG,
};
use std::collections::{BTreeMap, VecDeque};

pub struct Cursor<'a> {
  root: Port,
  prev: Port,
  path: &'a mut BTreeMap<u32, VecDeque<u8>>,
}

impl<'a> Cursor<'a> {
  fn next(&mut self, inet: &mut INet, slot: u8) -> Cursor {
    Cursor { root: self.root, prev: port(addr(enter(inet, self.prev)), slot as u32), path: self.path }
  }

  fn push_back(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_back(slot);
  }

  fn push_front(&mut self, kind: u32, slot: u8) {
    self.path.entry(kind).or_default().push_front(slot);
  }

  fn pop_back(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_back());
    self.cleanup(kind);
    opt
  }

  fn pop_front(&mut self, kind: u32) -> Option<u8> {
    let opt = self.path.get_mut(&kind).and_then(|vec| vec.pop_front());
    self.cleanup(kind);
    opt
  }

  fn cleanup(&mut self, kind: u32) {
    if self.path.get(&kind).map_or(false, |vec| vec.is_empty()) {
      self.path.remove(&kind);
    }
  }
}

// Checks if two interaction nets ports are equal.
pub fn equal(inet: &mut INet, function_book: &FunctionBook, a: Port, b: Port) -> bool {
  let mut a_path = BTreeMap::new();
  let mut b_path = BTreeMap::new();
  let mut a_cursor = Cursor { root: a, prev: a, path: &mut a_path };
  let mut b_cursor = Cursor { root: b, prev: b, path: &mut b_path };
  compare(inet, function_book, &mut a_cursor, &mut b_cursor)
}

// Compares two cursors by moving them forward until root is reached
pub fn compare(inet: &mut INet, function_book: &FunctionBook, a: &mut Cursor, b: &mut Cursor) -> bool {
  //println!("equal {} {} {:?} {:?}", a.prev, b.prev, a.path, b.path);
  //println!("== {}", crate::term::read_at(inet, a.prev));
  //println!("== {}", crate::term::read_at(inet, b.prev));

  // Moves one of the cursors forward and compares
  fn advance(inet: &mut INet, function_book: &FunctionBook, a: &mut Cursor, b: &mut Cursor) -> Option<bool> {
    reduce(inet, function_book, a.prev, &|ak, bk| ak == FIX || bk == FIX);

    let a_next = enter(inet, a.prev);
    let a_kind = kind(inet, addr(a_next));

    // If on root, stop
    if a_next == a.root || a_next == ROOT {
      return None;

    // If on a fixed point, stop
    } else if a_kind == FIX {
      return None;

    // If entering main port...
    } else if slot(enter(inet, a.prev)) == 0 {
      // If deque isn't empty, pop_back a slot and move to it
      if let Some(slot) = a.pop_back(a_kind) {
        //println!("enter main (pass)");
        let an = &mut a.next(inet, slot);
        let eq = compare(inet, function_book, an, b);
        a.push_back(a_kind, slot);
        return Some(eq);

      // If deque is empty, move to slots [1,2] and push_front to the *other* deque
      } else {
        //println!("enter main (split)");
        for slot in [2, 1] {
          b.push_front(a_kind, slot);
          let an = &mut a.next(inet, slot);
          let eq = compare(inet, function_book, an, b);
          b.pop_front(a_kind);
          if !eq {
            return Some(false);
          }
        }
        return Some(true);
      }

    // If entering an aux port, push_back that slot to the deque, and move to the main port
    } else {
      //println!("enter aux");
      a.push_back(a_kind, slot(enter(inet, a.prev)) as u8);
      let an = &mut a.next(inet, 0);
      let eq = compare(inet, function_book, an, b);
      a.pop_back(a_kind);
      return Some(eq);
    }
  }

  // If 'a' can be advanced, advance it and compare
  if let Some(eq) = advance(inet, function_book, a, b) {
    return eq;
  }

  // If 'b' can be advanced, advance it and compare
  if let Some(eq) = advance(inet, function_book, b, a) {
    return eq;
  }

  // If both are fixed-point, check `@x (f (g x)) == @x (g (f x))`
  let a_next = enter(inet, a.prev);
  let b_next = enter(inet, b.prev);
  if kind(inet, addr(a_next)) == FIX && kind(inet, addr(b_next)) == FIX {
    // If both ports are different, apply the fixpose transformation and compare
    if a_next != b_next {
      fixpose(inet, a_next, b_next);
      return compare(inet, function_book, a, b);
    }
    // If both ports are identical on slot 2, enter the merged fixpoint and compare
    if slot(a_next) == 2 {
      let a = &mut a.next(inet, 0);
      let b = &mut b.next(inet, 0);
      return compare(inet, function_book, a, b);
    }
  }

  //println!("check {:?} == {:?}", a.path, b.path);

  // If we've reached a final port (root or fix), compare the unconsumed paths
  return a.path.get(&CON) == b.path.get(&CON);
}
