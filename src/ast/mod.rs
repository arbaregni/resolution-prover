mod expr;
pub use expr::*;

mod parse;
pub use parse::*;

#[cfg(test)]
mod tests {
    use crate::ast;
    use crate::ast::{Expr, ExprKind, parse};

    #[test]
    fn parse_simple_0() {
        let source = "llama";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Literal("llama").into())
    }
    #[test]
    fn parse_simple_1() {
        let source = "sweet or sour or something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Or(vec![
            ExprKind::Literal("sweet").into(),
            ExprKind::Literal("sour").into(),
            ExprKind::Literal("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_2() {
        let source = "hot and spicy and something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::And(vec![
            ExprKind::Literal("hot").into(),
            ExprKind::Literal("spicy").into(),
            ExprKind::Literal("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_3() {
        let source = "tasty implies good";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::If(
            ExprKind::Literal("tasty").into(),
            ExprKind::Literal("good").into(),
        ).into()
        )
    }

    #[test]
    fn parse_failure_0() {
        let source = "if and when";
        let _ = parse(source).expect_err("`if` is reserved and should error");
    }
    #[test]
    fn parse_failure_1() {
        let source = "this implies that implies something";
        let _ = parse(source).expect_err("implies can not be chained");
    }
    #[test]
    fn parse_failure_2() {
        let source = "red and blue or green and orange";
        let _ = parse(source).expect_err("ambigious operators not allowed");
    }
    #[test]
    fn parse_failure_3() {
        let source = "x or and";
        let _ = parse(source).expect_err("should reject a reserved word in this position");
    }

    #[test]
    fn parse_nested_0() {
        let source = "(red and blue) or (green and orange)";
        let expr = match parse(source) {
            Ok(expr) => expr,
            Err(why) => {
                eprintln!("{}", why);
                panic!("`{}` should parse", source);
            }
        };
        assert_eq!(expr, ExprKind::Or(vec![
            ExprKind::And(vec![
                ExprKind::Literal("red").into(),
                ExprKind::Literal("blue").into(),
            ]).into(),
            ExprKind::And(vec![
                ExprKind::Literal("green").into(),
                ExprKind::Literal("orange").into(),
            ]).into(),
        ]).into());
    }
    #[test]
    fn parse_nested_1() {
        let source = "red and (blue or green) and orange";
        let expr = match parse(source) {
            Ok(expr) => expr,
            Err(why) => {
                eprintln!("{}", why);
                panic!("`{}` should parse", source);
            }
        };
        assert_eq!(expr, ExprKind::And(vec![
            ExprKind::Literal("red").into(),
            ExprKind::Or(vec![
                ExprKind::Literal("blue").into(),
                ExprKind::Literal("green").into(),
            ]).into(),
            ExprKind::Literal("orange").into(),
        ]).into());
    }
    #[test]
    fn parse_nested_2() {
        let source = "((ace implies king) or (king implies ace)) and not ( (ace implies king) and (king implies ace) )";
        let expr = match parse(source) {
            Ok(expr) => expr,
            Err(why) => {
                eprintln!("{}", why);
                panic!("`{}` should parse", source);
            }
        };
        assert_eq!(expr, ExprKind::And(vec![
            ExprKind::Or(vec![
                ExprKind::If(
                    ExprKind::Literal("ace").into(),
                    ExprKind::Literal("king").into(),
                ).into(),
                ExprKind::If(
                    ExprKind::Literal("king").into(),
                    ExprKind::Literal("ace").into(),
                ).into(),
            ]).into(),
            ExprKind::Not(
                ExprKind::And(vec![
                    ExprKind::If(
                        ExprKind::Literal("ace").into(),
                        ExprKind::Literal("king").into(),
                    ).into(),
                    ExprKind::If(
                        ExprKind::Literal("king").into(),
                        ExprKind::Literal("ace").into(),
                    ).into(),
                ]).into(),
            ).into(),
        ]).into())
    }


}
