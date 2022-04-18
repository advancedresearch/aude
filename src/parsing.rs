//! Parsing.

use crate::*;

use piston_meta::{Convert, Range};

fn parse_expr(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut expr: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = convert.meta_f64("num") {
            convert.update(range);
            expr = Some(ConstF64(F64Val(val)));
        } else if let Ok((range, _)) = convert.meta_bool("f64") {
            convert.update(range);
            expr = Some(Ty(F64));
        } else if let Ok((range, val)) = convert.meta_f64("type_n") {
            convert.update(range);
            expr = Some(Ty(TypeN(val as usize)));
        } else if let Ok((range, _)) = convert.meta_bool("id") {
            convert.update(range);
            expr = Some(Fun(Id));
        } else if let Ok((range, _)) = convert.meta_bool("sin") {
            convert.update(range);
            expr = Some(Fun(Sin));
        } else if let Ok((range, _)) = convert.meta_bool("cos") {
            convert.update(range);
            expr = Some(Fun(Cos));
        } else if let Ok((range, _)) = convert.meta_bool("neg") {
            convert.update(range);
            expr = Some(Fun(Neg));
        } else if let Ok((range, _)) = convert.meta_bool("mul") {
            convert.update(range);
            expr = Some(Fun(Mul));
        } else if let Ok((range, _)) = convert.meta_bool("add") {
            convert.update(range);
            expr = Some(Fun(Add));
        } else if let Ok((range, _)) = convert.meta_bool("fst_par") {
            convert.update(range);
            expr = Some(Fun(FstPar));
        } else if let Ok((range, _)) = convert.meta_bool("snd_par") {
            convert.update(range);
            expr = Some(Fun(SndPar));
        } else if let Ok((range, _)) = convert.meta_bool("fst") {
            convert.update(range);
            expr = Some(Fun(Fst));
        } else if let Ok((range, _)) = convert.meta_bool("snd") {
            convert.update(range);
            expr = Some(Fun(Snd));
        } else if let Ok((range, val)) = convert.meta_f64("var") {
            convert.update(range);
            expr = Some(Var(val as usize));
        } else if let Ok((range, val)) = parse_bin("bin", convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_app("app", convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let expr = expr.ok_or(())?;
    Ok((convert.subtract(start), expr))
}

fn parse_app(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>,
) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut f: Option<Expr> = None;
    let mut args: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("f", convert, ignored) {
            convert.update(range);
            f = Some(val);
        } else if let Ok((range, val)) = parse_expr("arg", convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let mut f = f.ok_or(())?;
    for arg in args.into_iter() {
        f = app(f, arg);
    }
    Ok((convert.subtract(start), f))
}

fn parse_bin(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>,
) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut in_ty_expr: Option<Expr> = None;
    let mut out_ty_expr: Option<Expr> = None;
    let mut op: Option<Op> = None;
    let mut meta: Vec<Meta> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, _)) = convert.meta_bool("fun") {
            convert.update(range);
            op = Some(Op::Fun);
        } else if let Ok((range, _)) = convert.meta_bool("lin_fun") {
            convert.update(range);
            op = Some(Op::Fun);
            meta.push(Meta::IsLinear(true));
        } else if let Ok((range, _)) = convert.meta_bool("lin_lam") {
            convert.update(range);
            op = Some(Op::Lam);
            meta.push(Meta::IsLinear(true));
        } else if let Ok((range, _)) = convert.meta_bool("par") {
            convert.update(range);
            op = Some(Op::Par);
        } else if let Ok((range, _)) = convert.meta_bool("tup") {
            convert.update(range);
            op = Some(Op::Tup);
        } else if let Ok((range, _)) = convert.meta_bool("comp_lin") {
            convert.update(range);
            op = Some(Op::Comp);
            meta.push(Meta::IsLinear(true));
        } else if let Ok((range, _)) = convert.meta_bool("comp") {
            convert.update(range);
            op = Some(Op::Comp);
        } else if let Ok((range, _)) = convert.meta_bool("ty") {
            convert.update(range);
            op = Some(Op::Ty);
        } else if let Ok((range, _)) = convert.meta_bool("lam") {
            convert.update(range);
            op = Some(Op::Lam);
        } else if let Ok((range, _)) = convert.meta_bool("app") {
            convert.update(range);
            op = Some(Op::App);
        } else if let Ok((range, val)) = parse_expr("a", convert, ignored) {
            convert.update(range);
            in_ty_expr = Some(val);
        } else if let Ok((range, val)) = parse_expr("b", convert, ignored) {
            convert.update(range);
            out_ty_expr = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let in_ty_expr = in_ty_expr.ok_or(())?;
    let out_ty_expr = out_ty_expr.ok_or(())?;
    let op = op.ok_or(())?;
    if op == Op::Lam && !meta.iter().any(|n| if let Meta::IsLinear(_) = n {true} else {false}) {
        meta.push(Meta::IsLinear(false));
    }
    Ok((convert.subtract(start), Op(op, Box::new((in_ty_expr, out_ty_expr)), meta)))
}

/// Parses an expression string.
pub fn parse_str(data: &str) -> Result<Expr, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_expr("expr", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}
