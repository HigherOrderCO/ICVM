// Term parser and stringifier. Grammar:
// <Term> ::= <Lam> | <App> | <Sup> | <Dup> | <Var> | <Set>
// <Lam>  ::= "λ" <name> <Term>
// <App>  ::= "(" <Term> <Term> ")"
// <Ann>  ::= "<" <Term> ":" <Term> ")"
// <Sup>  ::= "{" <Term> <Term> "}" ["#" <tag>]
// <Dup>  ::= "dup" ["#" <tag>] <name> <name> "=" <Term> [";"] <Term>
// <Fix>  ::= "@" <name> <Term>
// <Var>  ::= <name>
// <Set>  ::= "*"
// <name> ::= <alphanumeric_name>
// <tag>  ::= <positive_integer>

use std::assert_matches::debug_assert_matches;

use itertools::Itertools;

use super::*;

// Parses a name, returns the remaining code and the name.
fn is_name_char(c: Chr) -> bool {
  false
    || (c >= b'A' && c <= b'Z')
    || (c >= b'a' && c <= b'z')
    || (c >= b'0' && c <= b'9')
    || (c == b'_')
    || (c == b'.')
}

fn parse_name(code: &Str) -> (&Str, &Str) {
  let code = skip_whitespace(code);
  let mut i: usize = 0;
  while i < code.len() && is_name_char(code[i]) {
    i += 1;
  }
  (&code[i ..], &code[0 .. i])
}

fn skip_whitespace(code: &Str) -> &Str {
  let mut i: usize = 0;
  while i < code.len() && (code[i] == b' ' || code[i] == b'\n') {
    i += 1;
  }
  &code[i ..]
}

fn parse_text<'a>(code: &'a Str, text: &Str) -> Result<&'a Str, String> {
  let code = skip_whitespace(code);
  if code.starts_with(text) {
    Ok(&code[text.len() ..])
  } else {
    Err(format!("Expected '{}', found '{}'", String::from_utf8_lossy(text), String::from_utf8_lossy(code)))
  }
}

// Parses a term, returns the remaining code and the term.
pub fn parse_term<'a>(
  code: &'a Str,
  ctx: &mut Context<'a>,
  idx: &mut u32,
  functions: &mut HashMap<String, Term>,
) -> (&'a Str, Term) {
  let code = skip_whitespace(code);
  match code[0] {
    // Comment: `// many words here ... <newline>`
    b'/' if code[1] == b'/' => {
      let end = code.iter().position(|&c| c == b'\n').unwrap_or(code.len());
      parse_term(&code[end ..], ctx, idx, functions)
    }
    // Definition: `def nam = val; bod` (note: ';' is optional)
    b'd' if code.starts_with(b"def ") => {
      let (code, nam) = parse_name(&code[4 ..]);
      let code = parse_text(code, b"=").unwrap();
      let (code, val) = parse_term(code, ctx, idx, functions);
      debug_assert_matches!(val, Lam { .. }, "Definitions must be lambda terms");
      let code = if code[0] == b';' { &code[1 ..] } else { code };
      // extend(nam, Some(val.clone()), ctx);
      let name = String::from_utf8_lossy(nam).to_string();
      assert!(functions.insert(name.clone(), val).is_none(), "Duplicate definition: {name}");
      let (code, bod) = parse_term(code, ctx, idx, functions);
      // narrow(ctx);
      (code, bod)
    }
    // Typed Abstraction: `λ(var: Type) body`
    b'\xce' if code[1] == b'\xbb' && code[2] == b'(' => {
      let (code, nam) = parse_name(&code[3 ..]);
      let code = parse_text(code, b":").unwrap();
      let (code, typ) = parse_term(code, ctx, idx, functions);
      let code = parse_text(code, b")").unwrap();
      extend(nam, None, ctx);
      let (code, bod) = parse_term(code, ctx, idx, functions);
      narrow(ctx);
      let nam = nam.to_vec();
      let typ = Some(Box::new(typ));
      let bod = Box::new(bod);
      (code, Lam { nam, typ, bod })
    }
    // Untyped Abstraction: `λvar body`
    b'\xce' if code[1] == b'\xbb' => {
      let (code, nam) = parse_name(&code[2 ..]);
      extend(nam, None, ctx);
      let (code, bod) = parse_term(code, ctx, idx, functions);
      narrow(ctx);
      let nam = nam.to_vec();
      let typ = None;
      let bod = Box::new(bod);
      (code, Lam { nam, typ, bod })
    }
    // Application: `(func argm1 argm2 ... argmN)`
    b'(' => {
      let (mut code, mut fun) = parse_term(&code[1 ..], ctx, idx, functions);
      while code[0] != b')' {
        let (new_code, arg) = parse_term(code, ctx, idx, functions);
        code = new_code;
        let arg = Box::new(arg);
        fun = App { fun: Box::new(fun), arg };
      }
      let code = parse_text(code, b")").unwrap();
      (code, fun)
    }
    // Annotation: `<val:typ>`
    b'<' => {
      let (code, val) = parse_term(&code[1 ..], ctx, idx, functions);
      let code = parse_text(code, b":").unwrap();
      let (code, typ) = parse_term(code, ctx, idx, functions);
      let code = parse_text(code, b">").unwrap();
      (code, Ann { val: Box::new(val), typ: Box::new(typ) })
    }
    // Pair: `{val0 val1}#tag` (note: '#tag' is optional)
    b'{' => {
      let (code, fst) = parse_term(&code[1 ..], ctx, idx, functions);
      let (code, snd) = parse_term(code, ctx, idx, functions);
      let code = parse_text(code, b"}").unwrap();
      let (code, tag) = if code[0] == b'#' { parse_name(&code[1 ..]) } else { (code, &b""[..]) };
      let tag = name_to_index(&tag.to_vec());
      let fst = Box::new(fst);
      let snd = Box::new(snd);
      (code, Sup { tag, fst, snd })
    }
    // Dup: `dup #tag fst snd = val; bod` (note: '#tag' and ';' are optional)
    b'd' if code.starts_with(b"dup ") => {
      let code = &code[4 ..];
      let (code, tag) = if code[0] == b'#' { parse_name(&code[1 ..]) } else { (code, &b""[..]) };
      let (code, fst) = parse_name(code);
      let (code, snd) = parse_name(code);
      let code = parse_text(code, b"=").unwrap();
      extend(snd, None, ctx);
      extend(fst, None, ctx);
      let (code, val) = parse_term(code, ctx, idx, functions);
      let code = if code[0] == b';' { &code[1 ..] } else { code };
      let (code, nxt) = parse_term(code, ctx, idx, functions);
      narrow(ctx);
      narrow(ctx);
      let tag = name_to_index(&tag.to_vec());
      let fst = fst.to_vec();
      let snd = snd.to_vec();
      let val = Box::new(val);
      let nxt = Box::new(nxt);
      (code, Dup { tag, fst, snd, val, nxt })
    }
    // Fix: `@name body`
    b'@' => {
      let (code, nam) = parse_name(&code[1 ..]);
      let (code, bod) = parse_term(code, ctx, idx, functions);
      let nam = nam.to_vec();
      let bod = Box::new(bod);
      (code, Fix { nam, bod })
    }
    // Set: `*`
    b'*' => (&code[1 ..], Set),
    // Variable: `<alphanumeric_name>`
    _ => {
      let (code, nam) = parse_name(code);
      let mut val: Option<Term> = None;
      for i in (0 .. ctx.len()).rev() {
        if ctx[i].0 == nam {
          match ctx[i].1 {
            Some(ref term) => {
              let name = nam.clone().to_vec();
              val = Some(copy(&name, *idx, term));
              *idx += 1;
              break;
            }
            None => {
              break;
            }
          }
        }
      }
      let nam = nam.to_vec();
      (code, match val {
        Some(term) => term,
        None => Var { nam },
      })
    }
  }
}

/// Functions that match on scott-encoded args can be split
/// to have a jump-table for the cases
/// E.g. λn (n (λp (S (S (F p)))) Z)
/// case S => λp (S (S (F p)))
/// case Z => Z
pub fn build_jump_table(
  function: &Term,
  function_name_to_term: &HashMap<String, Term>,
) -> Option<Vec<(Term, usize)>> {
  match &function {
    Lam { nam, typ: _, bod } => {
      let mut ctx = vec![nam];

      let mut next_inner_app = &**bod;
      let mut jump_table = vec![];
      // A case-matching function has structure λx (x arg1 arg2 ... argN)
      // N is the number of constructor variants: There's one handler for each variant
      while !matches!(next_inner_app, Var { nam: n } if n == nam) {
        match next_inner_app {
          App { fun, arg } => {
            // For handling the constructor cases, each arg must be a lambda (or reference to a
            // defined function). We determine how many nested lambdas each arg consists of,
            // this is >= the number of args of each constructor. E.g. in
            // def Z = λs λz (z)
            // def S = λn λs λz (s n)
            // λn (n (λp (S (S (F p)))) Z)
            // `λp (S (S (F p)))` has 1 λ, Z has 2 (>= 0, the number of args of the Z constructor)
            // So this `nested_lambda_count` gives us an upper bound for how many CON nodes we must
            // walk through, when checking if fast dispatch is possible when applying `function`
            // to an arg. Then we can exit the arg net walk early after `nested_lambda_count` CON
            // nodes, as we know that the arg doesn't have the net structure for fast dispatch.
            let mut nested_lambda_count = 0;
            let mut next_inner_body = &**arg;
            loop {
              next_inner_body = match next_inner_body {
                Lam { nam, typ: _, bod } => {
                  ctx.push(nam);
                  &**bod
                }
                Var { nam } => {
                  if ctx.contains(&nam) {
                    // Bound variable
                    // E.g. in
                    // def Z = λs λz (z)
                    // def S = λn λs λz (s n)
                    // λn (n (λp (S (S (F p)))) Z)
                    // Z gets resolved, and then we end up with `Var { nam: "z" }`
                    // which is in `ctx`, so we stop here
                    break;
                  } else {
                    let nam = std::str::from_utf8(nam).unwrap();
                    match function_name_to_term.get(nam) {
                      Some(Lam { nam, typ: _, bod }) => {
                        ctx.push(nam);
                        &**bod
                      }
                      Some(_) => {
                        // Definitions must be lambda terms => Function table contains only lambda terms
                        unreachable!()
                      }
                      None => {
                        // Free variable, not in `ctx`
                        // break;
                        unreachable!() // Free variables aren't allowed currently
                      }
                    }
                  }
                }
                _ => break,
              };
              nested_lambda_count += 1;
            }
            // Each arg must be a case handler (lambda)
            if nested_lambda_count == 0 {
              return None;
            }

            jump_table.push(((**arg).clone(), nested_lambda_count));
            next_inner_app = fun;
          }
          _ => return None,
        }
      }
      jump_table.reverse(); // Args were pushed in reverse order (outermost application first)
      // If `jump_table` is empty, e.g. `λx (x)`, it's not a case-matching function.
      // If `jump_table` only has one entry, e.g. `λx (x y)`, no allocations would be saved by using a jump table
      // (jump_table.len() > 1).then_some(jump_table)
      (!jump_table.is_empty()).then_some(jump_table)
    }
    _ => None,
  }
}

pub type FunctionName = String;
pub type FunctionId = u32;

pub struct FunctionBook {
  pub function_name_to_term: HashMap<FunctionName, Term>,
  pub function_id_to_terms: Vec<(Term, Option<Vec<(Term, usize)>>)>,
  pub function_id_to_name: Vec<FunctionName>,
  pub function_name_to_id: HashMap<FunctionName, FunctionId>,
}

impl FunctionBook {
  fn new(function_name_to_term: HashMap<String, Term>) -> Self {
    let function_name_to_terms = function_name_to_term
      .iter()
      .map(|(name, term)| {
        let jump_table = build_jump_table(&term, &function_name_to_term);
        (name, (term, jump_table))
      })
      .collect::<HashMap<_, _>>();

    let (function_id_to_name, function_id_to_terms): (Vec<_>, Vec<_>) = function_name_to_terms
      .into_iter()
      .sorted_by_key(|&(name, _)| name)
      .map(|(name, (term, jump_table_terms))| (name.clone(), (term.clone(), jump_table_terms.clone())))
      .unzip();

    let function_name_to_id = function_id_to_name
      .iter()
      .enumerate()
      .map(|(i, name)| (name.to_owned(), i as FunctionId))
      .collect::<HashMap<FunctionName, FunctionId>>();

    Self { function_name_to_term, function_id_to_terms, function_id_to_name, function_name_to_id }
  }
}

// Converts a source-code to a λ-term.
pub fn from_string<'a>(code: &'a Str) -> (Term, FunctionBook) {
  let mut ctx = Vec::new();
  let mut functions = HashMap::new();
  let mut idx = 0;
  let term = parse_term(code, &mut ctx, &mut idx, &mut functions).1;
  (term, FunctionBook::new(functions))
}

// Converts a λ-term back to a source-code.
pub fn to_string(term: &Term) -> Vec<Chr> {
  fn stringify_term(code: &mut Vec<u8>, term: &Term) {
    match term {
      &Lam { ref nam, ref typ, ref bod } => {
        code.extend_from_slice("λ".as_bytes());
        if let Some(ref t) = typ {
          code.extend_from_slice(b"(");
          code.append(&mut nam.clone());
          code.extend_from_slice(b": ");
          stringify_term(code, &t);
          code.extend_from_slice(b")");
        } else {
          code.append(&mut nam.clone());
        }
        code.extend_from_slice(b" ");
        stringify_term(code, &bod);
      }
      &App { ref fun, ref arg } => {
        code.extend_from_slice(b"(");
        stringify_term(code, &fun);
        code.extend_from_slice(b" ");
        stringify_term(code, &arg);
        code.extend_from_slice(b")");
      }
      &Ann { ref val, ref typ } => {
        code.extend_from_slice(b"<");
        stringify_term(code, &val);
        code.extend_from_slice(b": ");
        stringify_term(code, &typ);
        code.extend_from_slice(b">");
      }
      &Sup { tag, ref fst, ref snd } => {
        code.extend_from_slice(b"[");
        stringify_term(code, &fst);
        code.extend_from_slice(b" ");
        stringify_term(code, &snd);
        if tag != 0 {
          code.extend_from_slice(b"#");
          code.append(&mut index_to_name(tag));
        }
        code.extend_from_slice(b"]");
      }
      &Dup { tag, ref fst, ref snd, ref val, ref nxt } => {
        code.extend_from_slice(b"dup ");
        if tag != 0 {
          code.extend_from_slice(b"#");
          code.append(&mut index_to_name(tag));
          code.extend_from_slice(b" ");
        }
        code.append(&mut fst.clone());
        code.extend_from_slice(b" ");
        code.append(&mut snd.clone());
        code.extend_from_slice(b" = ");
        stringify_term(code, &val);
        code.extend_from_slice(b"; ");
        stringify_term(code, &nxt);
      }
      &Fix { ref nam, ref bod } => {
        code.extend_from_slice(b"@");
        code.append(&mut nam.clone());
        code.extend_from_slice(b" ");
        stringify_term(code, &bod);
      }
      &Set => {
        code.extend_from_slice(b"*");
      }
      &Var { ref nam } => {
        code.append(&mut nam.clone());
      }
    }
  }
  let mut code = Vec::new();
  stringify_term(&mut code, &term);
  return code;
}
