use crate::*;

use std::fmt::{Debug};
use std::hash::Hash;
use std::cell::RefCell;
use std::time::{Instant,Duration};
use serde::{Serialize, Deserialize};


/// env[i] is the value at $i
pub type Env<D> = Vec<Val<D>>;

/// a value can either be some domain specific value Dom(D) like an Int,
/// or it can be a primitive function or partially applied primitive function like + or (+ 2)
/// or it can be a lambda function with some captured env like (lam (* $1 $0)) where $1 may have been captured from
/// the surrounding code and this whole object may now be passed around
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Val<D: Domain> {
    Dom(D),
    PrimFun(CurriedFn<D>), // function ptr, arity, any args that have been partially filled in
    LamClosure(Idx, Env<D>), // body, captured env
    Thunk(Idx, Env<D>)
}

pub type VResult<D> = Result<Val<D>,VError>;
pub type VError = String;



#[derive(Debug)]
pub struct Evaluator<'a, D: Domain> {
    pub expr: Expr<'a>,
    pub data: RefCell<D::Data>,
    pub start_and_timelimit: Option<(Instant, Duration)>,
    pub dsl: &'a DSL<D>,
}

impl<'a> Expr<'a> {
    pub fn eval<D:Domain>(&self, env: &[Val<D>], dsl: &DSL<D>, timelimit: Option<Duration>) -> VResult<D> {
        self.as_eval(dsl, timelimit).eval_child(self.idx, env)
    }
    pub fn as_eval<D:Domain>(self, dsl: &'a DSL<D>, timelimit: Option<Duration>) -> Evaluator<'a, D> {
        let start_and_timelimit = timelimit.map(|d| (Instant::now(),d));
        Evaluator {
            expr: self,
            data: Default::default(),
            start_and_timelimit,
            dsl
        }
    }
}


/// Wraps a DSL function in a struct that manages currying of the arguments
/// which are fed in one at a time through .apply(). Example: the "+" primitive
/// evaluates to a CurriedFn with arity 2 and empty partial_args. The expression
/// (app + 3) evals to a CurriedFn with vec![3] as the partial_args. The expression
/// (app (app + 3) 4) will evaluate to 7 (since .apply() will fill the last argument,
/// notice that all arguments are filled, and return the result).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CurriedFn<D: Domain> {
    name: Symbol,
    arity: usize,
    partial_args: Env<D>,
}

impl<D: Domain> CurriedFn<D> {
    pub fn new(name: Symbol, arity: usize) -> Self {
        Self {
            name,
            arity,
            partial_args: Vec::new(),
        }
    }
    pub fn new_with_args(name: Symbol, arity: usize, partial_args: Env<D>) -> Self {
        Self {
            name,
            arity,
            partial_args,
        }
    }
    /// Feed one more argument into the function, returning a new CurriedFn if
    /// still not all the arguments have been received. Evaluate the function
    /// if all arguments have been received. Does not mutate the original.
    pub fn apply(&self, arg: Val<D>, handle: &Evaluator<D>) -> VResult<D> {
        let mut new_dslfn = self.clone();
        new_dslfn.partial_args.push(arg);
        if new_dslfn.partial_args.len() == new_dslfn.arity {
            handle.dsl.productions.get(&new_dslfn.name).unwrap().fn_ptr.unwrap() (new_dslfn.partial_args, handle)
        } else {
            Ok(Val::PrimFun(new_dslfn))
        }
    }
}

impl<D: Domain> Val<D> {
    pub fn dom(self) -> Result<D,VError> {
        match self {
            Val::Dom(d) => Ok(d),
            _ => Err("Val::unwrap_dom: not a domain value".into())
        }
    }
    #[inline(always)]
    pub fn unthunk(self, handle: &Evaluator<D>) -> VResult<D> {
        if let Val::Thunk(idx,env) = self {
            handle.eval_child(idx, env.as_slice())
        } else {
            Ok(self)
        }
    }
}


impl<D: Domain> From<D> for Val<D> {
    fn from(d: D) -> Self {
        Val::Dom(d)
    }
}

pub trait FromVal<D: Domain>: Sized {
    fn from_val(val: Val<D>) -> Result<Self,VError>;
}

impl<D: Domain> FromVal<D> for Val<D> {
    fn from_val(val: Val<D>) -> Result<Self,VError> {
        Ok(val)
    }
}


impl<'a, D: Domain> Evaluator<'a,D> {
    // apply a function (Val) to an argument (LazyVal)
    pub fn apply(&self, f: &Val<D>, x: Val<D>) -> VResult<D> {
        match f {
            Val::PrimFun(f) => f.apply(x, self),
            Val::LamClosure(f, env) => {
                let mut new_env = vec![x];
                new_env.extend(env.iter().cloned());
                self.eval_child(*f, &mut new_env)
            }
            // _ => Err(format!("Expected function or closure, got {:?}", f)),
            _ => Err("Expected function or closure".into()),
        }
    }

    pub fn set_timeout(&mut self, timeout: Duration) {
        self.start_and_timelimit = Some((Instant::now(), timeout))
    }

    /// eval a subexpression in an environment
    pub fn eval_child(&self, child: Idx, env: &[Val<D>]) -> VResult<D> {
        if let Some((start_time, duration)) = &self.start_and_timelimit {
            if start_time.elapsed() >= *duration {
                return Err("Eval Timeout".to_string());
            }
        }
        let val = match self.expr.get_node(child) {
            Node::Var(i) => {
                env[*i as usize].clone()
            }
            Node::IVar(_) => {
                panic!("attempting to execute a #i ivar")
            }
            Node::App(f,x) => {
                let f_val = self.eval_child(*f, env)?;
                let x_val = Val::Thunk(*x, env.to_vec());
                self.apply(&f_val, x_val)?
            }
            Node::Prim(p) => {
                match self.dsl.val_of_prim(p) {
                    Some(v) => v,
                    None => panic!("Prim `{}` not found",p),
                }
            }
            Node::Lam(b) => {
                Val::LamClosure(*b, env.to_vec())
            }
        };
        Ok(val)
    }
}
