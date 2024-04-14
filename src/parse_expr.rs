use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display, Formatter},
};

use crate::expr::*;

/// Takes a string, parses it into an Expr, then returns that string printed back out.
/// This normalizes the string eg all `lambda` gets converted to `lam` etc.
pub fn reparse(s: &str) -> String {
    let mut e = ExprSet::empty(Order::ChildFirst, false, false);
    let idx = e.parse_extend(s).unwrap();
    e.get(idx).to_string()
}

/// printing a single node prints the operator
impl Display for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(i, tag) => {
                write!(f, "${}", i)?;
                if *tag != -1 {
                    write!(f, "_{}", tag)?;
                }
                Ok(())
            }
            Self::Prim(p) => write!(f, "{}", p),
            Self::App(_, _) => write!(f, "app"),
            Self::Lam(_, tag) => {
                write!(f, "lam")?;
                if *tag != -1 {
                    write!(f, "_{}", tag)?;
                }
                Ok(())
            }
            Self::IVar(i) => write!(f, "#{}", i),
            Node::NVar(name) => write!(f, "${}", name),
            Node::NLinkVar(name, _link) => write!(f, "${}", name),
            Node::Let { .. } => write!(f, "let"),
            Node::RevLet { .. } => write!(f, "revlet"),
        }
    }
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_local(e: Expr, left_of_app: bool, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if e.idx == HOLE {
                return write!(f, "??");
            }

            match e.node() {
                Node::Var(_, _)
                | Node::IVar(_)
                | Node::Prim(_)
                | Node::NVar(_)
                | Node::NLinkVar(_, _) => {
                    write!(f, "{}", e.node())
                }
                Node::App(fun, x) => {
                    // if you are the left side of an application, and you are an application, you dont need parens
                    if !left_of_app {
                        write!(f, "(")?
                    }
                    fmt_local(e.get(*fun), true, f)?;
                    write!(f, " ")?;
                    fmt_local(e.get(*x), false, f)?;
                    if !left_of_app {
                        write!(f, ")")
                    } else {
                        Ok(())
                    }
                }
                Node::Lam(b, tag) => {
                    write!(f, "(lam")?;
                    if *tag != -1 {
                        write!(f, "_{}", tag)?;
                    }
                    write!(f, " ")?;
                    fmt_local(e.get(*b), false, f)?;
                    write!(f, ")")
                }
                Node::Let {
                    var,
                    type_str,
                    def,
                    body,
                } => {
                    write!(f, "let ${}::{} = ", var, type_str)?;
                    fmt_local(e.get(*def), false, f)?;
                    write!(f, " in ")?;
                    fmt_local(e.get(*body), false, f)
                }
                Node::RevLet {
                    inp_var,
                    def_vars,
                    def,
                    body,
                } => {
                    write!(f, "let ")?;
                    for (i, var) in def_vars.iter().enumerate() {
                        write!(f, "${}", var)?;
                        if i != def_vars.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, " = rev(${} = ", inp_var)?;
                    fmt_local(e.get(*def), false, f)?;
                    write!(f, ") in ")?;
                    fmt_local(e.get(*body), false, f)
                }
            }
        }
        fmt_local(*self, false, f)
    }
}

impl Display for ExprOwned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.immut())
    }
}

use nom::{
    branch::alt,
    bytes::complete::{tag, take_while, take_while1},
    character::complete::{alphanumeric1, digit1, multispace0},
    combinator::{eof, map_res, opt, recognize},
    error::Error,
    multi::{many0, many1, separated_list1},
    sequence::{preceded, terminated, tuple},
    IResult,
};

fn is_token_char(c: char) -> bool {
    c.is_alphanumeric() || "_\\-+*/'.<>|@?[],".contains(c)
}

fn parse_prim(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        take_while1(is_token_char),
        |p: &str| -> Result<Vec<Node>, Error<&str>> { Ok(vec![Node::Prim(p.into())]) },
    )(s)
}

fn parse_var(s: &str) -> IResult<&str, Vec<Node>> {
    preceded(
        tag("$"),
        map_res(
            tuple((
                map_res(digit1, str::parse),
                opt(preceded(tag("_"), map_res(digit1, str::parse))),
            )),
            |(i, var_tag)| -> Result<Vec<Node>, Error<&str>> {
                Ok(vec![Node::Var(i, var_tag.unwrap_or(-1))])
            },
        ),
    )(s)
}

fn parse_ivar(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(tag("#"), map_res(digit1, str::parse)),
        |i| -> Result<Vec<Node>, Error<&str>> { Ok(vec![Node::IVar(i)]) },
    )(s)
}

fn parse_nvar(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(tag("$"), take_while1(is_token_char)),
        |name: &str| -> Result<Vec<Node>, Error<&str>> {
            Ok(vec![Node::NLinkVar(name.into(), Idx::MAX)])
        },
    )(s)
}

fn parse_lam(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(
            tag("("),
            terminated(
                tuple((
                    alt((
                        preceded(
                            alt((tag("lambda_"), tag("lam_"))),
                            map_res(digit1, str::parse),
                        ),
                        map_res(
                            alt((tag("lambda"), tag("lam"))),
                            |_| -> Result<i32, Error<&str>> { Ok(-1) },
                        ),
                    )),
                    parse_program,
                )),
                tag(")"),
            ),
        ),
        |(tag, mut body)| -> Result<Vec<Node>, Error<&str>> {
            let node = Node::Lam(1, tag);
            body.push(node);
            Ok(body)
        },
    )(s)
}

fn parse_app(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(
            tag("("),
            terminated(tuple((parse_program, many1(parse_program))), tag(")")),
        ),
        |(mut f, mut xs)| -> Result<Vec<Node>, Error<&str>> {
            let rev_fix_symbol = crate::Symbol::from("rev_fix_param");
            let x_lengths = xs.iter().map(|x| x.len()).collect::<Vec<_>>();
            let mut lengths_sum: usize = x_lengths.iter().sum();
            let mut app_nodes = vec![];
            if f.len() == 1 {
                if let Node::Prim(n) = &f[0] {
                    if *n == rev_fix_symbol {
                        let fixer_var = xs[1][0].clone();
                        if let Node::NLinkVar(fixer_name, _) = fixer_var {
                            for x in xs[0].iter_mut() {
                                if let Node::NLinkVar(name, _) = x {
                                    if *name == fixer_name {
                                        *x = Node::NVar(name.clone());
                                    }
                                }
                            }
                            xs[1] = vec![Node::NVar(fixer_name.clone())];
                        }
                    }
                }
            }
            for (i, x) in xs.iter_mut().enumerate() {
                let node = if i == 0 {
                    Node::App(lengths_sum + 1, lengths_sum - x.len() + 1)
                } else {
                    Node::App(1, lengths_sum - x.len() + i + 1)
                };
                lengths_sum -= x.len();
                app_nodes.push(node);
                f.append(x);
            }
            f.append(&mut app_nodes);
            Ok(f)
        },
    )(s)
}

fn parse_type(s: &str) -> IResult<&str, &str> {
    recognize(tuple((
        alphanumeric1,
        opt(tuple((
            tag("("),
            parse_type,
            many0(tuple((tag(","), multispace0, parse_type))),
            tag(")"),
        ))),
    )))(s)
}

fn is_obj_char(c: char) -> bool {
    c.is_alphanumeric() || c == '-'
}

fn parse_object(s: &str) -> IResult<&str, &str> {
    recognize(tuple((
        take_while(is_obj_char),
        opt(tuple((
            tag("{"),
            parse_object,
            many0(tuple((tag(","), multispace0, parse_object))),
            tag("}"),
        ))),
        opt(alt((
            tuple((
                tag("("),
                parse_object,
                many0(tuple((tag(","), multispace0, parse_object))),
                tag(")"),
            )),
            tuple((
                tag("["),
                parse_object,
                many0(tuple((tag(","), multispace0, parse_object))),
                tag("]"),
            )),
        ))),
    )))(s)
}

fn parse_const(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        recognize(tuple((
            tag("Const("),
            parse_type,
            tag(","),
            multispace0,
            parse_object,
            tag(")"),
        ))),
        |p| -> Result<Vec<Node>, Error<&str>> { Ok(vec![Node::Prim(p.into())]) },
    )(s)
}

fn parse_let(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(
            tag("let $"),
            tuple((
                alphanumeric1,
                tag("::"),
                parse_type,
                tag(" = "),
                parse_program,
                tag(" in "),
                parse_program,
            )),
        ),
        |(var, _, type_str, _, mut def, _, mut body)| -> Result<Vec<Node>, Error<&str>> {
            let node = Node::Let {
                var: var.into(),
                type_str: type_str.into(),
                def: body.len() + 1,
                body: 1,
            };
            def.push(node.clone());
            def.append(&mut body);
            def.push(node);
            Ok(def)
        },
    )(s)
}

fn parse_let_rev(s: &str) -> IResult<&str, Vec<Node>> {
    map_res(
        preceded(
            tag("let "),
            tuple((
                separated_list1(tag(", "), preceded(tag("$"), alphanumeric1)),
                tag(" = rev("),
                preceded(tag("$"), alphanumeric1),
                tag(" = "),
                parse_program,
                tag(") in"),
                parse_program,
            )),
        ),
        |(def_vars, _, var, _, mut def, _, mut body)| -> Result<Vec<Node>, Error<&str>> {
            let node = Node::RevLet {
                inp_var: var.into(),
                def_vars: def_vars.into_iter().map(|s| s.into()).collect(),
                def: 1,
                body: def.len() + 1,
            };
            body.append(&mut def);
            body.push(node);
            Ok(body)
        },
    )(s)
}

fn parse_program(s: &str) -> IResult<&str, Vec<Node>> {
    preceded(
        multispace0,
        alt((
            parse_lam,
            parse_app,
            parse_var,
            parse_ivar,
            parse_nvar,
            parse_const,
            parse_let,
            parse_let_rev,
            parse_prim,
        )),
    )(s)
}

fn parse_full_program(s: &str) -> IResult<&str, Vec<Node>> {
    terminated(parse_program, eof)(s)
}

impl ExprSet {
    /// parses `s_init` as an Expr, inserting it into `self`. Uses .add() so spans
    /// and structural hashing are done automatically. Is order-aware.
    pub fn parse_extend(&mut self, s_init: &str) -> Result<Idx, String> {
        let init_len = self.nodes.len();

        let s = s_init.trim();
        // println!("parsing: {}", s_init);

        let match_res: IResult<&str, Vec<Node>> = parse_full_program(s);

        if let Err(nom::Err::Error(Error {
            input: _,
            code: nom::error::ErrorKind::Eof,
        })) = match_res
        {
            let wrapped_s = format!("({})", s);
            let wrapped_res = self.parse_extend(wrapped_s.as_str());
            if let Ok(e) = wrapped_res {
                return Ok(e);
            }
        };

        let nodes = match_res.map_err(|e| e.to_string())?.1;

        let mut items: Vec<Idx> = vec![];
        let mut named_vars_links: HashMap<crate::Symbol, Idx> = HashMap::new();
        let mut mult_def_vars: HashSet<crate::Symbol> = HashSet::new();
        let mut finished_lets = 0;
        let mut finished_lets_before: HashMap<crate::Symbol, usize> = HashMap::new();

        for node in nodes {
            // println!("node: {:?}", node);
            let norm_node = match node {
                Node::Prim(_) | Node::Var(_, _) | Node::IVar(_) | Node::NVar(_) => node,
                Node::App(f, x) => Node::App(items[items.len() - f], items[items.len() - x]),
                Node::Lam(b, tag) => Node::Lam(items[items.len() - b], tag),
                Node::NLinkVar(ref name, _) => {
                    if !mult_def_vars.contains(name) && named_vars_links.contains_key(name) {
                        Node::NLinkVar(name.clone(), named_vars_links[&name])
                    } else {
                        Node::NVar(name.clone())
                    }
                }
                Node::Let {
                    var,
                    type_str,
                    def,
                    body,
                } => {
                    if named_vars_links.contains_key(&var) {
                        let def_shift = finished_lets - finished_lets_before[&var];
                        finished_lets += 1;
                        Node::Let {
                            var,
                            type_str,
                            def: items[items.len() + def_shift - def],
                            body: items[items.len() - body],
                        }
                    } else {
                        let var_link = items.len() - 1;
                        named_vars_links.insert(var.clone(), items[var_link]);
                        finished_lets_before.insert(var, finished_lets);
                        continue;
                    }
                }
                Node::RevLet {
                    inp_var,
                    def_vars,
                    def,
                    body,
                } => {
                    let var_link = items[items.len() - def];
                    if named_vars_links.contains_key(&inp_var)
                        && named_vars_links[&inp_var] != var_link
                    {
                        mult_def_vars.insert(inp_var.clone());
                    } else {
                        named_vars_links.insert(inp_var.clone(), var_link);
                    }
                    Node::RevLet {
                        inp_var,
                        def_vars,
                        def: var_link,
                        body: items[items.len() - body],
                    }
                }
            };
            // println!("norm_node: {:?}", norm_node);
            items.push(self.add(norm_node));
            // println!("last_node: {}", items[items.len() - 1]);
        }
        if self.order == Order::ParentFirst {
            self.nodes[init_len..].reverse();
        }
        Ok(items[items.len() - 1])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_parse(set: &mut ExprSet, in_s: &str, out_s: &str) {
        let e = set.parse_extend(in_s).unwrap();
        assert_eq!(set.get(e).to_string(), out_s.to_string());
    }

    #[test]
    fn test_parse() {
        let set = &mut ExprSet::empty(Order::ChildFirst, false, false);
        assert_parse(set, "(+ 2 3)", "(+ 2 3)");
        assert_parse(set, "(+ 2 3)", "(+ 2 3)");

        assert_parse(set, "3", "3");
        assert_parse(set, "foo", "foo");

        assert_parse(set, "(foo (bar baz))", "(foo (bar baz))");
        assert_parse(set, "((foo bar) baz)", "(foo bar baz)");

        assert_parse(set, "foo bar baz", "(foo bar baz)");

        assert_parse(set, "(lam b)", "(lam b)");
        assert_parse(set, "(lambda b)", "(lam b)");

        assert_parse(
            set,
            "(lambda (fix1 $0 (lambda (lambda (if (empty? (cdr $0)) (cdr $0) (cons (car $0) ($1 (cdr $0))))))))",
            "(lam (fix1 $0 (lam (lam (if (empty? (cdr $0)) (cdr $0) (cons (car $0) ($1 (cdr $0))))))))"
        );

        assert_parse(set, "lam b", "(lam b)");
        assert_parse(set, "(foo (lam b) (lam c))", "(foo (lam b) (lam c))");
        assert_parse(set, "(lam (+ a b))", "(lam (+ a b))");
        assert_parse(set, "(lam (+ $0 b))", "(lam (+ $0 b))");
        assert_parse(set, "(lam (+ #0 b))", "(lam (+ #0 b))");
        assert_parse(set, "Const(list(int), Any[])", "Const(list(int), Any[])");
        assert_parse(set, "Const(int, -1)", "Const(int, -1)");
        assert_parse(set, "let $v1::int = 1 in $v1", "let $v1::int = 1 in $v1");
        assert_parse(
            set,
            "let $v1::list(int) = Const(list(int), Any[]) in let $v2::list(int) = Const(list(int), Any[0]) in \
                let $v3::list(int) = (concat $v1 $v2) in (concat $inp0 $v3)",
            "let $v1::list(int) = Const(list(int), Any[]) in let $v2::list(int) = Const(list(int), Any[0]) in \
            let $v3::list(int) = (concat $v1 $v2) in (concat $inp0 $v3)"
        );
        assert_parse(
            set,
            "let $v1, $v2 = rev($inp0 = (cons $v1 $v2)) in let $v3::int = 0 in let $v4::int = Const(int, -1) in \
            let $v5::int = (- $v3 $v4) in let $v6::list(int) = (repeat $v1 $v5) in (concat $inp0 $v6)",
            "let $v1, $v2 = rev($inp0 = (cons $v1 $v2)) in let $v3::int = 0 in let $v4::int = Const(int, -1) in \
            let $v5::int = (- $v3 $v4) in let $v6::list(int) = (repeat $v1 $v5) in (concat $inp0 $v6)"
        );

        let e = set.parse_extend("$3").unwrap();
        assert_eq!(set.get(e).node(), &Node::Var(3, -1));
        let e = set.parse_extend("#3").unwrap();
        assert_eq!(set.get(e).node(), &Node::IVar(3));

        let e = set.parse_extend("$3_1").unwrap();
        assert_eq!(set.get(e).node(), &Node::Var(3, 1));

        let e = set.parse_extend("$23_145").unwrap();
        assert_eq!(set.get(e).node(), &Node::Var(23, 145));

        let e = set.parse_extend("$23_0").unwrap();
        assert_eq!(set.get(e).node(), &Node::Var(23, 0));

        let e = set.parse_extend("(lam_123 (+ $0_1 $1_1))").unwrap();
        let (_, tag) = match set.get(e).node() {
            Node::Lam(body, tag) => (*body, *tag),
            x => panic!("expected lam, got {}", x),
        };
        assert_eq!(tag, 123);

        assert_parse(set, "(lam_123 (+ $0_1 $1_1))", "(lam_123 (+ $0_1 $1_1))");

        assert_parse(
            set,
            "(fix1 $0 (lam (lam (if (empty? $0) $0 (cons (+ 1 (car $0)) ($1 (cdr $0)))))))",
            "(fix1 $0 (lam (lam (if (empty? $0) $0 (cons (+ 1 (car $0)) ($1 (cdr $0)))))))",
        )
    }
}
