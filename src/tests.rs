use crate::{inet::*, term::*};
use itertools::Itertools;

#[test]
fn test_equal() {
  pub fn get_body(inet: &INet, host: Port) -> Port {
    return port(addr(enter(inet, host)), 2);
  }

  pub fn get_func(inet: &INet, host: Port) -> Port {
    return port(addr(enter(inet, host)), 0);
  }

  pub fn get_argm(inet: &INet, host: Port) -> Port {
    return port(addr(enter(inet, host)), 1);
  }

  let code = "
// Church arithmetic
def zero = λs λz (z)
def succ = λn λs λz dup s0 s1 = s; (s0 (n s1 z))
def mul = λn λm λs (n (m s))

// Church consts
def c1 = λf λx (f x)
def c2 = λf λx (dup #b f0 f1 = f; (f0 (f1 x)))
def c3 = λf λx (dup #c f0 f1 = f; dup #c f2 f3 = f0; (f1 (f2 (f3 x))))
def p1 = c2          // 2
def p2 = (mul c2 p1) // 4
def p3 = (mul c2 p2) // 8
def p4 = (mul c2 p3) // 16
def p5 = (mul c2 p4) // 32
def p6 = (mul c2 p5) // 64
def p7 = (mul c2 p6) // 128
def p8 = (mul c2 p7) // 256

// Booleans
def true = λt λf t
def false = λt λf f
def not = λb ((b false) true)
def neg = λb λt λf (b f t)

// Lists
def cons = λhead λtail λcons λnil (cons head tail)
def nil = λcons λnil nil
def head = λlist (list λhλt(h) λx(x))
def tail = λlist (list λhλt(t) nil)

def map = @map λf λxs
  dup #f f0 f1 = f;
  (xs λhead λtail (cons (f0 head) (map f1 tail)) nil)

def ids = @k λcons λnil (cons λx(x) k)
def nums = @x (cons zero (map succ x))
def inf = @inf λs λz (s inf)

def f0 = @x (cons true (cons true (cons false x)))
def f1 = @x (cons true (cons true (cons false (cons true (cons true (cons false x))))))

λt (t f0 f1)

//(head (tail (tail (tail ids))))

";

  //  Creates initial term
  let (term, function_book) = from_string(code.as_bytes());

  println!("{:#?}", function_book.function_name_to_term);
  println!("{}", term);
  println!("{:?}", term);

  // Creates the net from term
  let mut inet = new_inet();
  alloc_at(&mut inet, &term, ROOT, &function_book);

  // Equal
  let body = get_body(&inet, ROOT);
  let arg0 = get_argm(&inet, get_func(&inet, body));
  let arg1 = get_argm(&inet, body);
  //println!("{}", read_at(&inet, ROOT));
  println!("a = {}", read_at(&inet, arg0, &function_book));
  println!("b = {}", read_at(&inet, arg1, &function_book));
  let eq = equal(&mut inet, &function_book, arg0, arg1);
  println!("");
  println!("[[a==b : {}]]", eq);
  assert!(eq);

  // Normal
  //normal(&mut inet, ROOT);
  //println!("itt {}", read_at(&inet, ROOT));
  //println!("lam {}", lambda_term_from_inet(&inet));
  //println!("{:?} rewrites", inet.rules);
}

#[test]
fn test_build_jump_table() {
  fn expect_jump_table(code: &str, expected_jump_table: Option<Vec<(String, usize)>>) {
    let (term, function_book) = from_string(code.as_bytes());
    let jump_table = build_jump_table(&term, &function_book.function_name_to_term).map(|jt| {
      jt.into_iter().map(|(term, nested_lambda_count)| (term.to_string(), nested_lambda_count)).collect_vec()
    });
    assert_eq!(jump_table, expected_jump_table);
  }

  // case S => λp (S (S (F p)))
  // case Z => Z
  expect_jump_table(
    "
    def Z = λs λz (z)
    def S = λn λs λz (s n)
    λn (n (λp (S (S (F p)))) Z)",
    Some(vec![("λp (S (S (F p)))".into(), 1), ("Z".into(), 2)]),
  );

  expect_jump_table(
    "λn (n (λp (S (S (F p)))) λs λz (z))",
    Some(vec![("λp (S (S (F p)))".into(), 1), ("λs λz z".into(), 2)]),
  );

  expect_jump_table("λn (n (λp (S (S (F p)))) Z)", None);

  // case S => λp (p)
  // case Z => Z
  expect_jump_table(
    "
    def Z = λs λz (z)
    λn (n (λp(p)) Z)",
    Some(vec![("λp p".into(), 1), ("Z".into(), 2)]),
  );

  // This calls `x`, not `n`, thus it's not suitable for fast dispatch
  expect_jump_table("λn (x (λp (S (S (F p)))) Z)", None);

  // Also not suitable
  expect_jump_table("λn (n)", None);
}
