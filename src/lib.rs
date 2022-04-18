#![deny(missing_docs)]

//! # Aude
//!
//! An automated differentiation solver with a Lisp-like functional programming language

use Function::*;
use Expr::*;
use Type::*;

use std::fmt;

pub mod parsing;

/// Stores operator.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    /// Composition (of functions).
    Comp,
    /// Parallel tuple.
    Par,
    /// Lambda.
    Lam,
    /// Type operator (`:`).
    Ty,
    /// Application (of function).
    App,
    /// Function type.
    Fun,
    /// Tuple.
    Tup,
}

/// Store a types.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    /// The `f64` type.
    F64,
    /// A cummulative type hierarchy.
    TypeN(usize),
}

/// Stores a function.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Function {
    /// Identity function.
    Id,
    /// Sine.
    Sin,
    /// Cosine.
    Cos,
    /// Negation.
    Neg,
    /// Multiplication.
    Mul,
    /// Addition.
    Add,
    /// The first element of a tuple.
    Fst,
    /// The second element of a tuple.
    Snd,
    /// The first element of a parallel tuple.
    FstPar,
    /// The second element of a parallel tuple.
    SndPar,
}

impl Function {
    /// Gets the type of the function.
    pub fn ty(&self) -> Expr {
        match self {
            Sin | Cos => fun(Ty(F64), Ty(F64)),
            Neg => lin(Ty(F64), Ty(F64)),
            Add => lin(tup(Ty(F64), Ty(F64)), Ty(F64)),
            Mul => fun(tup(Ty(F64), Ty(F64)), Ty(F64)),
            Fst => lam(Ty(TypeN(0)), lam(Ty(TypeN(0)), lin(tup(Var(1), Var(0)), Var(1)))),
            Snd => lam(Ty(TypeN(0)), lam(Ty(TypeN(0)), lin(tup(Var(1), Var(0)), Var(0)))),
            FstPar => lam(Ty(TypeN(0)), lam(Ty(TypeN(0)), lin(par(Var(1), Var(0)), Var(1)))),
            SndPar => lam(Ty(TypeN(0)), lam(Ty(TypeN(0)), lin(par(Var(1), Var(0)), Var(0)))),
            Id => lam(Ty(TypeN(0)), lin(Var(0), Var(0))),
        }
    }

    /// Gets the argument type, if any.
    pub fn arg_ty(&self) -> Option<Expr> {
        if let Op(Op::Fun, ab, _) = self.ty() {Some(ab.0.clone())}
        else {None}
    }

    /// Gets the return type, if any.
    pub fn ret_ty(&self) -> Option<Expr> {
        if let Op(Op::Fun, ab, _) = self.ty() {Some(ab.1.clone())}
        else {None}
    }
}

/// Used to wrap f64 for `Expr`.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct F64Val(pub f64);

impl Eq for F64Val {}
impl Ord for F64Val {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Represents an expression.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr {
    /// An f64 constant.
    ConstF64(F64Val),
    /// A variable (using DeBruijn index).
    Var(usize),
    /// A function.
    Fun(Function),
    /// A type.
    Ty(Type),
    /// A binary operation.
    Op(Op, Box<(Expr, Expr)>, Vec<Meta>),
}

/// Stores meta data.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Meta {
    /// Whether the expression is constant or not.
    IsConstant(bool),
    /// Whether the expression is linear or not.
    IsLinear(bool),
    /// A proof that expression is equal to another expression.
    IsEqTo(Option<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            ConstF64(F64Val(v)) => write!(w, "{}", v)?,
            Var(n) => write!(w, "${}", n)?,
            Fun(Id) => write!(w, "id")?,
            Fun(Sin) => write!(w, "sin")?,
            Fun(Cos) => write!(w, "cos")?,
            Fun(Neg) => write!(w, "neg")?,
            Fun(Mul) => write!(w, "mul")?,
            Fun(Add) => write!(w, "add")?,
            Fun(Fst) => write!(w, "fst")?,
            Fun(Snd) => write!(w, "snd")?,
            Fun(FstPar) => write!(w, "fst_par")?,
            Fun(SndPar) => write!(w, "snd_par")?,
            Ty(F64) => write!(w, "f64")?,
            Ty(TypeN(n)) => write!(w, "type({})", n)?,
            Op(Op::Fun, ab, _) => {
                if self.is_linear().unwrap_or(false) {
                    write!(w, "(lin {} {})", ab.0, ab.1)?
                } else {
                    write!(w, "(fun {} {})", ab.0, ab.1)?
                }
            }
            Op(Op::Lam, ab, _) => {
                if self.is_linear().unwrap_or(false) {
                    write!(w, "(lin_lam {} {})", ab.0, ab.1)?
                } else {
                    write!(w, "(lam {} {})", ab.0, ab.1)?
                }
            }
            Op(Op::Par, ab, _) => write!(w, "(par {} {})", ab.0, ab.1)?,
            Op(Op::Tup, ab, _) => write!(w, "(tup {} {})", ab.0, ab.1)?,
            Op(Op::Ty, ab, _) => write!(w, "(ty {} {})", ab.0, ab.1)?,
            Op(Op::Comp, ab, _) => {
                if self.is_linear().unwrap_or(false) {
                    write!(w, "(comp_lin {} {})", ab.0, ab.1)?
                } else {
                    write!(w, "(comp {} {})", ab.0, ab.1)?
                }
            }
            Op(Op::App, ab, _) => write!(w, "{}({})", ab.0, ab.1)?,
        }
        Ok(())
    }
}

impl Expr {
    /// Sets meta knowledge.
    pub fn set_meta(&mut self, flag: Meta) -> Result<(), ()> {
        match self {
            Op(_, _, ref mut meta) => {
                for m in meta.iter_mut() {
                    if &*m == &flag {return Ok(())}
                }
                meta.push(flag);
                Ok(())
            }
            _ => Err(())
        }
    }

    /// Remove meta knowledge.
    pub fn remove_meta(&mut self, flag: Meta) -> Result<(), ()> {
        match self {
            Op(_, _, ref mut meta) => {
                for i in 0..meta.len() {
                    if meta[i] == flag {
                        meta.swap_remove(i);
                        return Ok(());
                    }
                }
                Ok(())
            }
            _ => Err(())
        }
    }

    /// Gets meta knowledge.
    pub fn get_meta(&self, flag: Meta) -> bool {
        match self {
            Op(_, _, ref meta) => {
                for m in meta {
                    if m == &flag {return true}
                }
                false
            }
            _ => false
        }
    }

    /// Gets "is constant" meta knowledge.
    pub fn get_meta_is_constant(&self) -> Option<bool> {
        match self {
            Op(_, _, ref meta) => {
                for m in meta {
                    if let Meta::IsConstant(v) = m {return Some(*v)}
                }
                None
            }
            _ => None,
        }
    }

    /// Gets "is linear" meta knowledge.
    pub fn get_meta_is_linear(&self) -> Option<bool> {
        match self {
            Op(_, _, ref meta) => {
                for m in meta {
                    if let Meta::IsLinear(v) = m {return Some(*v)}
                }
                None
            }
            _ => None,
        }
    }

    /// Returns `Ok(true)` if expression has a proof in meta data that it is equal to something.
    pub fn get_meta_is_eq_to_something(&self) -> Option<bool> {
        match self {
            Op(_, _, ref meta) => {
                for m in meta {
                    match m {
                        Meta::IsEqTo(Some(_)) => return Some(true),
                        Meta::IsEqTo(None) => return Some(false),
                        _ => {}
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Return `Ok(true)` if one expression is equal to another using meta data.
    pub fn is_eq_to(&self, other: &Expr) -> Option<bool> {
        if self == other {Some(true)}
        else {
            match self {
                Op(_, _, ref meta) => {
                    for m in meta {
                        if let Meta::IsEqTo(Some(f)) = m {
                            if f == other {return Some(true)}
                        }
                    }
                }
                _ => {}
            };
            match other {
                Op(_, _, ref meta) => {
                    for m in meta {
                        if let Meta::IsEqTo(Some(f)) = m {
                            if f == self {return Some(true)}
                        }
                    }
                }
                _ => {}
            };
            None
        }
    }

    /// Analyzes expression.
    ///
    /// Returns `true` if meta knowledge changed.
    pub fn analyze(&mut self) -> bool {
        let mut res = false;
        if let Op(_, ab, _) = self {
            res |= ab.0.analyze();
            res |= ab.1.analyze();
        }

        let meta_is_eq_to_something = self.get_meta_is_eq_to_something();
        if meta_is_eq_to_something.is_none() {
            let mut eq: Option<Expr> = None;
            match self {
                Op(Op::Lam, ab, _) => {
                    match &ab.1 {
                        Var(0) => {
                            let mut f = app(Fun(Id), ab.0.clone());
                            f.analyze();
                            eq = Some(f);
                        }
                        Op(Op::App, a_ab, _) => {
                            let mut f = app(Fun(Id), ab.0.clone());
                            f.analyze();
                            if a_ab.0.is_eq_to(&f).unwrap_or(false) {
                                eq = Some(f);
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
            if let Some(f) = &eq {
                let linear = f.is_linear().unwrap_or(false);
                let _ = self.remove_meta(Meta::IsLinear(!linear));
                let _ = self.set_meta(Meta::IsLinear(linear));
            }
            let _ = self.set_meta(Meta::IsEqTo(eq));
            res = true;
        }

        let meta_is_constant = self.get_meta_is_constant();
        if meta_is_constant.is_none() {
            match self {
                Op(Op::App | Op::Lam, ab, _) => {
                    let flag = ab.1.is_constant().unwrap();
                    let _ = self.set_meta(Meta::IsConstant(flag));
                    res = true;
                }
                Op(Op::Tup | Op::Par, ab, _) => {
                    let flag = ab.0.is_constant().unwrap() &&
                               ab.1.is_constant().unwrap();
                    let _ = self.set_meta(Meta::IsConstant(flag));
                    res = true;
                }
                Op(Op::Fun, _, _) => {
                    let _ = self.set_meta(Meta::IsConstant(true));
                    res = true;
                }
                _ => {}
            }
        }

        let meta_is_linear = self.get_meta_is_linear();
        if meta_is_linear.is_none() {
            let ref mut ctx = vec![];
            match self.ty(ctx) {
                Some(ty) => match ty.is_linear() {
                    Ok(x) => {
                        let _ = self.set_meta(Meta::IsLinear(x));
                        res = true;
                    }
                    Err(_) => {}
                }
                None => {}
            }
        }
        let meta_is_linear = self.get_meta_is_linear();
        if meta_is_linear.is_none() {
            match self {
                Op(Op::Tup | Op::Par | Op::Comp, ab, _) => {
                    let flag = ab.0.is_linear().unwrap_or(false) &&
                               ab.1.is_linear().unwrap_or(false);
                    let _ = self.set_meta(Meta::IsLinear(flag));
                    res = true;
                }
                Op(Op::Fun, _, _) => {
                    let _ = self.set_meta(Meta::IsLinear(false));
                    res = true;
                }
                _ => {}
            }
        }

        if let Op(_, _, meta) = self {meta.sort()};
        res
    }

    /// Gets the argument type, if any.
    pub fn arg_ty(&self) -> Option<Expr> {
        match self {
            Op(Op::Fun, ab, _) => Some(ab.0.clone()),
            _ => None,
        }
    }

    /// Gets the return type, if any.
    pub fn ret_ty(&self) -> Option<Expr> {
        match self {
            Op(Op::Fun, ab, _) => Some(ab.1.clone()),
            _ => None,
        }
    }

    /// Gets the second part of the expression.
    pub fn snd(&self) -> Option<Expr> {
        match self {
            Op(Op::Tup, ab, _) => Some(ab.1.clone()),
            // Todo: Might need better normalisation.
            Op(Op::Lam, ab, _) => ab.1.snd(),
            _ => None,
        }
    }

    /// Derviate expression.
    pub fn deriv(&self, ctx: &mut Vec<Expr>) -> Option<Expr> {
        if self.is_linear().unwrap_or(false) {
            let ty = self.ty(ctx)?;
            return Some(lam_lin(ty.arg_ty()?, tup(app(self.clone(), Var(0)), self.clone())))
        }
        match self {
            Fun(f) => Some(lam(f.arg_ty()?, tup(app(Fun(f.clone()), Var(0)), match f {
                Sin => lam_lin(Ty(F64), mul(Var(0), app(Fun(Cos), Var(1)))),
                Cos => lam_lin(Ty(F64), mul(Var(0), app(Fun(Neg), app(Fun(Sin), Var(1))))),
                Mul => lam_lin(tup(Ty(F64), Ty(F64)),
                           add(mul(app(fst(Ty(F64), Ty(F64)), Var(0)),
                                   app(fst(Ty(F64), Ty(F64)), Var(1))),
                               mul(app(snd(Ty(F64), Ty(F64)), Var(0)),
                                   app(snd(Ty(F64), Ty(F64)), Var(1))))),
                _ => return None,
            }))),
            Op(Op::Par, ab, _) => {
                // `a0 -> a1`
                let a = ab.0.clone();
                // `b0 -> b1`
                let b = ab.1.clone();
                // `a0 -> (a1, a0 -o a1)`
                let da = ab.0.deriv(ctx)?;
                // `b0 -> (b1, b0 -o b1)`
                let db = ab.1.deriv(ctx)?;
                let a_ty = ab.0.ty(ctx)?;
                let b_ty = ab.1.ty(ctx)?;
                // `a0`
                let a_arg_ty = a_ty.arg_ty()?;
                // `b0`
                let b_arg_ty = b_ty.arg_ty()?;
                // `a1`
                let a_ret_ty = a_ty.ret_ty()?;
                // `b1`
                let b_ret_ty = b_ty.ret_ty()?;
                let arg_ty = par(a_arg_ty.clone(), b_arg_ty.clone());
                let fst_v = app(fst_par(a_arg_ty.clone(), b_arg_ty.clone()), Var(0));
                let snd_v = app(snd_par(a_arg_ty.clone(), b_arg_ty.clone()), Var(0));
                // `snd(a1)(a0 -o a1)`
                let snd_a = snd(a_ret_ty.clone(), lin(a_arg_ty, a_ret_ty));
                // `snd(b1)(b0 -o b1)`
                let snd_b = snd(b_ret_ty.clone(), lin(b_arg_ty, b_ret_ty));
                Some(lam(arg_ty.clone(),
                     tup(par(app(a, fst_v.clone()), app(b, snd_v.clone())),
                         lam_lin(arg_ty, par(app(snd_a, app(da, fst_v)),
                                             app(snd_b, app(db, snd_v)))))))
            }
            Op(Op::Comp, ab, _) => {
                let a = ab.0.clone();
                let b = ab.1.clone();
                let da = ab.0.deriv(ctx)?;
                let db = ab.1.deriv(ctx)?;
                let a_ty = a.ty(ctx)?;
                let a_arg_ty = a_ty.arg_ty()?;
                let a_ret_ty = a_ty.ret_ty()?;
                let b_ty = b.ty(ctx)?;
                let b_arg_ty = b_ty.arg_ty()?;
                let b_ret_ty = b_ty.arg_ty()?;
                let snd_a = snd(a_ret_ty.clone(), lin(a_arg_ty.clone(), a_ret_ty));
                let snd_b = snd(b_ret_ty.clone(), lin(b_arg_ty.clone(), b_ret_ty));
                Some(lam(a_arg_ty,
                         tup(app(a, app(b.clone(), Var(0))),
                             comp_lin(app(snd_b, app(da, app(b, Var(0)))),
                                      app(snd_a, app(db, Var(0)))))))
            }
            _ => None,
        }
    }

    /// Returns `Ok(true)` if the expression is constant.
    pub fn is_constant(&self) -> Result<bool, ()> {
        match self {
            ConstF64(_) => Ok(true),
            Var(0) => Ok(false),
            Var(_) | Ty(_) | Fun(_) => Ok(true),
            _ => {
                match self.get_meta_is_constant() {
                    Some(x) => Ok(x),
                    None => Err(())
                }
            }
        }
    }

    /// Returns `Ok(true)` if the expression is linear.
    pub fn is_linear(&self) -> Result<bool, ()> {
        match self {
            Ty(_) => Ok(false),
            Fun(f) => f.ty().is_linear(),
            _ => {
                match self.get_meta_is_linear() {
                    Some(x) => Ok(x),
                    None => Err(())
                }
            }
        }
    }

    /// Evaluate expression.
    pub fn eval(&self, ctx: &mut Vec<Expr>, off: usize) -> Option<Expr> {
        match self {
            Var(n) => {
                let ctx_len = ctx.len();
                if *n >= off && *n < ctx_len + off {
                    Some(ctx[ctx_len - 1 - (n - off)].clone())
                } else {
                    Some(Var(*n))
                }
            }
            Ty(_) => Some(self.clone()),
            Op(Op::Lam, ab, _) => Some(lam(ab.0.eval(ctx, off)?, ab.1.eval(ctx, off + 1)?)),
            Op(Op::Fun, ab, _) => {
                let f = if self.is_linear().unwrap_or(false) {lin} else {fun};
                Some(f(ab.0.eval(ctx, off)?, ab.1.eval(ctx, off)?))
            }
            Op(Op::Tup, ab, _) => Some(tup(ab.0.eval(ctx, off)?, ab.1.eval(ctx, off)?)),
            Op(Op::Par, ab, _) => Some(par(ab.0.eval(ctx, off)?, ab.1.eval(ctx, off)?)),
            Op(Op::App, ab, _) => {
                if let Op(Op::Lam, a_ab, _) = &ab.0 {
                    let n = ctx.len();
                    ctx.push(ab.1.clone());
                    let res = a_ab.1.eval(ctx, off);
                    ctx.truncate(n);
                    res
                } else {
                    None
                }
            }
            _ => unimplemented!("{}", self),
        }
    }

    /// Computes the type of an expression.
    pub fn ty(&self, ctx: &mut Vec<Expr>) -> Option<Expr> {
        match self {
            ConstF64(_) => Some(Ty(F64)),
            Var(n) => {
                let ctx_len = ctx.len();
                if *n < ctx_len {
                    Some(ctx[ctx_len - 1 - n].clone())
                } else {
                    None
                }
            }
            Ty(TypeN(n)) => Some(Ty(TypeN(n + 1))),
            Ty(F64) => Some(Ty(TypeN(0))),
            Fun(f) => Some(f.ty()),
            Op(Op::Par, ab, _) => {
                let mut a_ty = ab.0.ty(ctx)?;
                a_ty.analyze();
                let mut b_ty = ab.1.ty(ctx)?;
                b_ty.analyze();
                let a_linear = a_ty.is_linear().ok()?;
                let b_linear = b_ty.is_linear().ok()?;
                if let Op(Op::Fun, a_ab, _) = &a_ty {
                    if let Op(Op::Fun, b_ab, _) = b_ty {
                        let a = a_ab.0.clone();
                        let b = b_ab.0;
                        let c = a_ab.1.clone();
                        let d = b_ab.1;
                        let f = if a_linear && b_linear {lin} else {fun};
                        return Some(f(par(a, b), par(c, d)))
                    }
                }
                Some(par(a_ty, b_ty))
            }
            Op(Op::Lam, ab, _) => {
                let a = ab.0.clone();
                let n = ctx.len();
                ctx.push(a.clone());
                let b = ab.1.ty(ctx);
                ctx.truncate(n);
                let b = b?;
                let f = match self.is_linear() {
                    Ok(true) => lin,
                    Ok(false) => fun,
                    Err(()) => return None,
                };
                Some(f(a.clone(), b))
            }
            Op(Op::Tup, ab, _) => {
                let a = ab.0.ty(ctx)?;
                let b = ab.1.ty(ctx)?;
                if a == Ty(TypeN(0)) && b == Ty(TypeN(0)) {Some(Ty(TypeN(0)))}
                else {Some(tup(a, b))}
            }
            Op(Op::App, ab, _) => {
                let a_ty = ab.0.ty(ctx)?;
                let mut b_ty = ab.1.ty(ctx)?;
                b_ty.analyze();
                match a_ty {
                    Op(Op::Fun, a_ab, _) => {
                        let mut arg_ty = a_ab.0;
                        arg_ty.analyze();
                        let ret_ty = a_ab.1;
                        if arg_ty == b_ty {
                            Some(ret_ty)
                        } else {
                            None
                        }
                    }
                    Op(Op::Lam, ref a_ab, _) => {
                        let mut arg_ty = a_ab.0.clone();
                        arg_ty.analyze();
                        if arg_ty == b_ty {
                            app(a_ty, ab.1.clone()).eval(ctx, 0)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            Op(Op::Fun, _, _) => Some(Ty(TypeN(0))),
            Op(Op::Comp, ab, _) => {
                let a_ty = ab.0.ty(ctx)?;
                let b_ty = ab.1.ty(ctx)?;
                let f = match self.is_linear() {
                    Ok(true) => lin,
                    Ok(false) => fun,
                    Err(()) => return None,
                };
                Some(f(a_ty.arg_ty()?, b_ty.ret_ty()?))
            }
            _ => unimplemented!("{:?}", self),
        }
    }
}

/// `fun`
pub fn fun(a: Expr, b: Expr) -> Expr {Op(Op::Fun, Box::new((a, b)), vec![])}
/// `tup`
pub fn tup(a: Expr, b: Expr) -> Expr {Op(Op::Tup, Box::new((a, b)), vec![])}
/// `lin`
pub fn lin(a: Expr, b: Expr) -> Expr {Op(Op::Fun, Box::new((a, b)), vec![Meta::IsLinear(true)])}
/// `par`
pub fn par(a: Expr, b: Expr) -> Expr {Op(Op::Par, Box::new((a, b)), vec![])}
/// `par_lin`
pub fn par_lin(a: Expr, b: Expr) -> Expr {Op(Op::Par, Box::new((a, b)), vec![Meta::IsLinear(true)])}
/// Function application.
pub fn app(a: Expr, b: Expr) -> Expr {Op(Op::App, Box::new((a, b)), vec![])}
/// `mul`
pub fn mul(a: Expr, b: Expr) -> Expr {app(Fun(Mul), tup(a, b))}
/// `add`
pub fn add(a: Expr, b: Expr) -> Expr {app(Fun(Add), tup(a, b))}
/// Construct lambda expression from type and body expression.
pub fn lam(a: Expr, b: Expr) -> Expr {Op(Op::Lam, Box::new((a, b)), vec![Meta::IsLinear(false)])}
/// `lam_lin`
pub fn lam_lin(a: Expr, b: Expr) -> Expr {Op(Op::Lam, Box::new((a, b)), vec![Meta::IsLinear(true)])}
/// `comp`
pub fn comp(a: Expr, b: Expr) -> Expr {Op(Op::Comp, Box::new((a, b)), vec![])}
/// `comp_lin`
pub fn comp_lin(a: Expr, b: Expr) -> Expr {Op(Op::Comp, Box::new((a, b)), vec![Meta::IsLinear(true)])}
/// `ty`
pub fn ty(a: Expr, b: Expr) -> Expr {Op(Op::Ty, Box::new((a, b)), vec![])}
/// `fst`
pub fn fst(t: Expr, u: Expr) -> Expr {app(app(Fun(Fst), t), u)}
/// `snd`
pub fn snd(t: Expr, u: Expr) -> Expr {app(app(Fun(Snd), t), u)}
/// `fst_par`
pub fn fst_par(t: Expr, u: Expr) -> Expr {app(app(Fun(FstPar), t), u)}
/// `snd_par`
pub fn snd_par(t: Expr, u: Expr) -> Expr {app(app(Fun(SndPar), t), u)}
/// `sin`
pub fn sin(a: Expr) -> Expr {app(Fun(Sin), a)}
/// `cos`
pub fn cos(a: Expr) -> Expr {app(Fun(Cos), a)}
/// `neg`
pub fn neg(a: Expr) -> Expr {app(Fun(Neg), a)}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parsing() {
        use parsing::parse_str;

        let a = parse_str("f64").unwrap();
        assert_eq!(a, Ty(F64));

        let a = parse_str("(fun f64 f64)").unwrap();
        assert_eq!(a, fun(Ty(F64), Ty(F64)));

        let a = parse_str("(lin f64 f64)").unwrap();
        assert_eq!(a, lin(Ty(F64), Ty(F64)));

        let a = parse_str("(par f64 f64)").unwrap();
        assert_eq!(a, par(Ty(F64), Ty(F64)));

        let a = parse_str("(tup f64 f64)").unwrap();
        assert_eq!(a, tup(Ty(F64), Ty(F64)));

        let a = parse_str("(tup f64 (fun f64 f64))").unwrap();
        assert_eq!(a, tup(Ty(F64), fun(Ty(F64), Ty(F64))));

        let a = parse_str("sin").unwrap();
        assert_eq!(a, Fun(Sin));

        let a = parse_str("cos").unwrap();
        assert_eq!(a, Fun(Cos));

        let a = parse_str("neg").unwrap();
        assert_eq!(a, Fun(Neg));

        let a = parse_str("(comp cos sin)").unwrap();
        assert_eq!(a, comp(Fun(Cos), Fun(Sin)));

        let a = parse_str("(ty sin (fun f64 f64))").unwrap();
        assert_eq!(a, ty(Fun(Sin), fun(Ty(F64), Ty(F64))));

        let a = parse_str("(fun f64 (fun f64 f64))").unwrap();
        assert_eq!(a, fun(Ty(F64), fun(Ty(F64), Ty(F64))));

        let a = parse_str("$0").unwrap();
        assert_eq!(a, Var(0));

        let a = parse_str(r#"(lam f64 $0)"#).unwrap();
        assert_eq!(a, lam(Ty(F64), Var(0)));

        let a = parse_str(r#"(lam f64 $0)"#).unwrap();
        assert_eq!(a, lam(Ty(F64), Var(0)));

        let a = parse_str(r#"(par (lam f64 $0) (lam f64 $0))"#).unwrap();
        assert_eq!(a, par(lam(Ty(F64), Var(0)), lam(Ty(F64), Var(0))));

        let a = parse_str("mul($0)($1)").unwrap();
        assert_eq!(a, app(app(Fun(Mul), Var(0)), Var(1)));

        let a = parse_str("add").unwrap();
        assert_eq!(a, Fun(Add));

        let a = parse_str("fst(f64)(f64)").unwrap();
        assert_eq!(a, fst(Ty(F64), Ty(F64)));

        let a = parse_str("snd(f64)(f64)").unwrap();
        assert_eq!(a, snd(Ty(F64), Ty(F64)));

        let a = parse_str("(fun (tup f64 f64) (tup f64 (lin (tup f64 f64) f64)))").unwrap();
        assert_eq!(a, fun(tup(Ty(F64), Ty(F64)), tup(Ty(F64), lin(tup(Ty(F64), Ty(F64)), Ty(F64)))));

        let a = parse_str(r#"(lam f64 (tup cos(sin($0)) (comp (lam f64 mul((tup $0 neg(sin($1)))))(sin($0)) (lam f64 mul((tup $0 cos($1))))($0))))"#).unwrap();
        assert_eq!(a, lam(
          Ty(F64),
          tup(
            cos(sin(Var(0))),
            comp(
              app(
                lam(Ty(F64), mul(Var(0), neg(sin(Var(1))))),
                sin(Var(0))
              ),
              app(
                lam(Ty(F64), mul(Var(0), cos(Var(1)))),
                Var(0)
              )
            )
          )
        ));
    }

    #[test]
    fn test_lin() {
        let a = lam_lin(Ty(F64), Var(0));
        assert!(a.is_linear().unwrap());

        let mut b = tup(a.clone(), a.clone());
        b.analyze();
        assert!(b.is_linear().unwrap());

        let mut b = par(a.clone(), a.clone());
        b.analyze();
        assert!(b.is_linear().unwrap());

        let mut a = fst(Ty(F64), Ty(F64));
        a.analyze();
        assert!(a.is_linear().unwrap());
    }

    #[test]
    fn test_eq() {
        let mut a = lam(Ty(F64), Var(0));
        a.analyze();
        let mut id = app(Fun(Id), Ty(F64));
        id.analyze();
        assert_eq!(a.is_eq_to(&id), Some(true));
        assert_eq!(id.is_eq_to(&a), Some(true));
    }

    #[test]
    fn test_ty() {
        fn check(f: &str, ty: &str) {
            use parsing::parse_str;

            let ref mut ctx = vec![];
            let mut a = parse_str(f).unwrap();
            a.analyze();
            let mut a_ty = a.ty(ctx).unwrap();
            a_ty.analyze();
            let mut ty = match parse_str(ty) {
                Ok(x) => x,
                Err(err) => {
                    eprintln!("{}", err);
                    panic!()
                }
            };
            ty.analyze();
            eprintln!("{} vs {}", a_ty, ty);
            assert_eq!(a_ty, ty);
        }

        check("sin", "(fun f64 f64)");
        check("f64", "type(0)");
        check("fst", "(lam type(0) (lam type(0) (lin (tup $1 $0) $1)))");
        check("fst(f64)", "(lam type(0) (lin (tup f64 $0) f64))");
        check("fst(f64)(f64)", "(lin (tup f64 f64) f64)");
        check("snd(f64)", "(lam type(0) (lin (tup f64 $0) $0))");
        check("snd(f64)((lin f64 f64))", "(lin (tup f64 (lin f64 f64)) (lin f64 f64))");
        check("fst_par(f64)", "(lam type(0) (lin (par f64 $0) f64))");
        check("fst_par(f64)(f64)", "(lin (par f64 f64) f64)");
        check("snd_par(f64)", "(lam type(0) (lin (par f64 $0) $0))");
        check("snd_par(f64)(f64)", "(lin (par f64 f64) f64)");
        check("(lam (par (tup f64 f64) (tup f64 f64)) (tup (par mul(fst_par((tup f64 f64))((tup f64 f64))($0)) mul(snd_par((tup f64 f64))((tup f64 f64))($0))) (lin_lam (par (tup f64 f64) (tup f64 f64)) (par snd(f64)((lin (tup f64 f64) f64))((lam (tup f64 f64) (tup mul($0) (lin_lam (tup f64 f64) add((tup mul((tup fst(f64)(f64)($0) fst(f64)(f64)($1))) mul((tup snd(f64)(f64)($0) snd(f64)(f64)($1))))))))(fst_par((tup f64 f64))((tup f64 f64))($0))) snd(f64)((lin (tup f64 f64) f64))((lam (tup f64 f64) (tup mul($0) (lin_lam (tup f64 f64) add((tup mul((tup fst(f64)(f64)($0) fst(f64)(f64)($1))) mul((tup snd(f64)(f64)($0) snd(f64)(f64)($1))))))))(snd_par((tup f64 f64))((tup f64 f64))($0)))))))", "(fun (par (tup f64 f64) (tup f64 f64)) (tup (par f64 f64) (lin (par (tup f64 f64) (tup f64 f64)) (lin (par (tup f64 f64) (tup f64 f64)) (par f64 f64)))))");
        check("(comp sin sin)", "(fun f64 f64)");
        check("(lam f64 (tup sin(sin($0)) (comp_lin snd(f64)((lin f64 f64))((lam f64 (tup sin($0) (lin_lam f64 mul((tup $0 cos($1))))))(sin($0))) snd(f64)((lin f64 f64))((lam f64 (tup sin($0) (lin_lam f64 mul((tup $0 cos($1))))))($0)))))", "(fun f64 (tup f64 (lin f64 f64)))");
    }
}
