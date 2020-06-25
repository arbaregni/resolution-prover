mod literal;
pub use literal::*;

mod expr;
pub use expr::*;

mod parse;
pub use parse::*;


#[cfg(test)]
mod tests {
    use crate::ast::{ExprKind, parse, LiteralExpr, Expr};
    use crate::prover::ClosedClauseSet;
    use crate::ast;

    #[test]
    fn parse_simple_0() {
        let source = "llama";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, LiteralExpr::atom("llama").into())
    }
    #[test]
    fn parse_simple_1() {
        let source = "sweet or sour or something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Or(vec![
            LiteralExpr::atom("sweet").into(),
            LiteralExpr::atom("sour").into(),
            LiteralExpr::atom("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_2() {
        let source = "hot and spicy and something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::And(vec![
            LiteralExpr::atom("hot").into(),
            LiteralExpr::atom("spicy").into(),
            LiteralExpr::atom("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_3() {
        let source = "tasty implies good";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::If(
            LiteralExpr::atom("tasty").into(),
            LiteralExpr::atom("good").into(),
        ).into()
        )
    }
    #[test]
    fn parse_simple_4() {
        let source = "not pleasant";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Not(
            LiteralExpr::atom("pleasant").into()
        ).into())
    }
    #[test]
    fn parse_simple_5() {
        let source = "p iff q";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Iff(
            LiteralExpr::atom("p").into(),
            LiteralExpr::atom("q").into(),
        ).into())
    }
    #[test]
    fn parse_simple_6() {
        let source = "p xor q";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Xor(
            LiteralExpr::atom("p").into(),
            LiteralExpr::atom("q").into(),
        ).into())
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
                LiteralExpr::atom("red").into(),
                LiteralExpr::atom("blue").into(),
            ]).into(),
            ExprKind::And(vec![
                LiteralExpr::atom("green").into(),
                LiteralExpr::atom("orange").into(),
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
            LiteralExpr::atom("red").into(),
            ExprKind::Or(vec![
                LiteralExpr::atom("blue").into(),
                LiteralExpr::atom("green").into(),
            ]).into(),
            LiteralExpr::atom("orange").into(),
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
                    LiteralExpr::atom("ace").into(),
                    LiteralExpr::atom("king").into(),
                ).into(),
                ExprKind::If(
                    LiteralExpr::atom("king").into(),
                    LiteralExpr::atom("ace").into(),
                ).into(),
            ]).into(),
            ExprKind::Not(
                ExprKind::And(vec![
                    ExprKind::If(
                        LiteralExpr::atom("ace").into(),
                        LiteralExpr::atom("king").into(),
                    ).into(),
                    ExprKind::If(
                        LiteralExpr::atom("king").into(),
                        LiteralExpr::atom("ace").into(),
                    ).into(),
                ]).into(),
            ).into(),
        ]).into())
    }

    #[test]
    fn negate_normalize_0() {
        let expr: Expr =
            ExprKind::Not(
                ExprKind::Not(
                    ExprKind::Not(
                        ExprKind::Not(
                            ExprKind::Not(
                                LiteralExpr::atom("apple").into()
                            ).into()
                        ).into()
                    ).into()
            ).into()
        ).into();
        let normalized = ExprKind::Not(LiteralExpr::atom("apple").into()).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }

    #[test]
    fn negate_normalize_1() {
        let expr: Expr = ExprKind::Not(
            ExprKind::And(vec![
                LiteralExpr::atom("apple").into(),
                LiteralExpr::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                LiteralExpr::atom("apple").into()
            ).into(),
            ExprKind::Not(
                LiteralExpr::atom("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_2() {
        let expr: Expr = ExprKind::Not(
            ExprKind::And(vec![
                LiteralExpr::atom("apple").into(),
                LiteralExpr::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                LiteralExpr::atom("apple").into()
            ).into(),
            ExprKind::Not(
                LiteralExpr::atom("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_3() {
        let expr: Expr = ExprKind::Not(
            ExprKind::Or(vec![
                LiteralExpr::atom("apple").into(),
                LiteralExpr::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                LiteralExpr::atom("apple").into(),
            ).into(),
            ExprKind::Not(
                LiteralExpr::atom("banana").into(),
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }
    #[test]
    fn negate_normalize_4() {
        let expr: Expr = ExprKind::Not(
            ExprKind::Or(vec![
                LiteralExpr::atom("apple").into(),
                LiteralExpr::atom("banana").into(),
                ExprKind::Not(
                    ExprKind::And(vec![
                        LiteralExpr::atom("coconut").into(),
                        ExprKind::Not(
                            LiteralExpr::atom("dragonfruit").into(),
                        ).into()
                    ]).into()
                ).into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                LiteralExpr::atom("apple").into(),
            ).into(),
            ExprKind::Not(
                LiteralExpr::atom("banana").into(),
            ).into(),
            ExprKind::And(vec![
                LiteralExpr::atom("coconut").into(),
                ExprKind::Not(
                    LiteralExpr::atom("dragonfruit").into()
                ).into()
            ]).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }
    #[test]
    fn negate_normalize_5() {
        let expr: Expr = ExprKind::Or(vec![
            ExprKind::Or(vec![
                ExprKind::Or(vec![
                    ExprKind::Or(vec![
                        LiteralExpr::atom("a").into(),
                        LiteralExpr::atom("b").into(),
                    ]).into(),
                ]).into(),
                LiteralExpr::atom("c").into(),
            ]).into(),
            LiteralExpr::atom("d").into(),
            LiteralExpr::atom("e").into(),
            ExprKind::Or(vec![
                LiteralExpr::atom("f").into(),
            ]).into(),
            LiteralExpr::atom("g").into(),
            ExprKind::Or(vec![
                LiteralExpr::atom("h").into(),
            ]).into(),
            LiteralExpr::atom("i").into(),
        ]).into();
        let normalized = ExprKind::Or(vec![
            LiteralExpr::atom("a").into(),
            LiteralExpr::atom("b").into(),
            LiteralExpr::atom("c").into(),
            LiteralExpr::atom("d").into(),
            LiteralExpr::atom("e").into(),
            LiteralExpr::atom("f").into(),
            LiteralExpr::atom("g").into(),
            LiteralExpr::atom("h").into(),
            LiteralExpr::atom("i").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_6() {
        let expr: Expr = ExprKind::And(vec![
            ExprKind::And(vec![
                ExprKind::And(vec![
                    ExprKind::And(vec![
                        LiteralExpr::atom("p").into(),
                    ]).into(),
                    LiteralExpr::atom("q").into(),
                ]).into(),
                ExprKind::And(vec![
                    LiteralExpr::atom("r").into(),
                    LiteralExpr::atom("s").into(),
                    LiteralExpr::atom("t").into(),
                    LiteralExpr::atom("u").into(),
                ]).into(),
                ExprKind::And(vec![
                    LiteralExpr::atom("v").into(),
                    LiteralExpr::atom("w").into(),
                ]).into(),
            ]).into(),
            LiteralExpr::atom("x").into(),
            ExprKind::And(vec![
                LiteralExpr::atom("y").into(),
                LiteralExpr::atom("z").into(),
            ]).into(),
        ]).into();
        let normalized = ExprKind::And(vec![
            LiteralExpr::atom("p").into(),
            LiteralExpr::atom("q").into(),
            LiteralExpr::atom("r").into(),
            LiteralExpr::atom("s").into(),
            LiteralExpr::atom("t").into(),
            LiteralExpr::atom("u").into(),
            LiteralExpr::atom("v").into(),
            LiteralExpr::atom("w").into(),
            LiteralExpr::atom("x").into(),
            LiteralExpr::atom("y").into(),
            LiteralExpr::atom("z").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn normalize_negations_7() {
        let expr: Expr = ExprKind::Iff(
            ExprKind::Xor(
                LiteralExpr::atom("a").into(),
                LiteralExpr::atom("b").into(),
            ).into(),
            ExprKind::Not(
                ExprKind::Iff(
                    LiteralExpr::atom("a").into(),
                    LiteralExpr::atom("b").into(),
                ).into(),
            ).into(),
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Or(vec![
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        ExprKind::Not(LiteralExpr::atom("a").into()).into(),
                        LiteralExpr::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        LiteralExpr::atom("a").into(),
                        ExprKind::Not(LiteralExpr::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        LiteralExpr::atom("a").into(),
                        LiteralExpr::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        ExprKind::Not(LiteralExpr::atom("a").into()).into(),
                        ExprKind::Not(LiteralExpr::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
            ]).into(),
            ExprKind::Or(vec![
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        LiteralExpr::atom("a").into(),
                        LiteralExpr::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        ExprKind::Not(LiteralExpr::atom("a").into()).into(),
                        ExprKind::Not(LiteralExpr::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        ExprKind::Not(LiteralExpr::atom("a").into()).into(),
                        LiteralExpr::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        LiteralExpr::atom("a").into(),
                        ExprKind::Not(LiteralExpr::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
            ]).into()
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }

    #[test]
    fn to_clauses_0() {
        let expr: Expr = ExprKind::Or(vec![
            ExprKind::And(vec![
                LiteralExpr::atom("day").into(),
                LiteralExpr::atom("night").into(),
            ]).into(),
            ExprKind::And(vec![
                LiteralExpr::atom("love").into(),
                LiteralExpr::atom("war").into(),
            ]).into()
        ]).into();
        // (day and night) or (love and war)
        // (day or (love and war)) and (night or (love and war))
        // (day or love) and (day or war) and (night or love) and (night or war)
        let mut clause_set  = ClosedClauseSet::new();
        expr.into_clauses(&mut clause_set).expect("should not fail");

        assert_eq!(clause_set.clauses.len(), 4);
        assert!(clause_set.clauses.contains( &clause!(day, love) ));
        assert!(clause_set.clauses.contains( &clause!(day, war) ));
        assert!(clause_set.clauses.contains( &clause!(night, love) ));
        assert!(clause_set.clauses.contains( &clause!(night, war) ));
    }
    #[test]
    fn to_clauses_1() {
        let expr = ast::parse("((a => b) and (b => c)) => (a => c)").expect("should not fail");

        let mut clause_set  = ClosedClauseSet::new();
        expr.into_clauses(&mut clause_set).expect("should not error");

        assert_eq!(clause_set.clauses.len(), 0);
    }
}
