mod literal;
pub use literal::*;

mod expr;
pub use expr::*;

mod parse;
pub use parse::*;


#[cfg(test)]
mod tests {
    use crate::ast::{ExprKind, parse, Term, Expr};
    use crate::prover::ClosedClauseSet;
    use crate::ast;

    #[test]
    fn parse_simple_0() {
        let source = "llama";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, Term::atom("llama").into())
    }
    #[test]
    fn parse_simple_1() {
        let source = "sweet or sour or something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Or(vec![
            Term::atom("sweet").into(),
            Term::atom("sour").into(),
            Term::atom("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_2() {
        let source = "hot and spicy and something";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::And(vec![
            Term::atom("hot").into(),
            Term::atom("spicy").into(),
            Term::atom("something").into(),
        ]).into()
        )
    }
    #[test]
    fn parse_simple_3() {
        let source = "tasty implies good";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::If(
            Term::atom("tasty").into(),
            Term::atom("good").into(),
        ).into()
        )
    }
    #[test]
    fn parse_simple_4() {
        let source = "not pleasant";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Not(
            Term::atom("pleasant").into()
        ).into())
    }
    #[test]
    fn parse_simple_5() {
        let source = "p iff q";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Iff(
            Term::atom("p").into(),
            Term::atom("q").into(),
        ).into())
    }
    #[test]
    fn parse_simple_6() {
        let source = "p xor q";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Xor(
            Term::atom("p").into(),
            Term::atom("q").into(),
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
                Term::atom("red").into(),
                Term::atom("blue").into(),
            ]).into(),
            ExprKind::And(vec![
                Term::atom("green").into(),
                Term::atom("orange").into(),
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
            Term::atom("red").into(),
            ExprKind::Or(vec![
                Term::atom("blue").into(),
                Term::atom("green").into(),
            ]).into(),
            Term::atom("orange").into(),
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
                    Term::atom("ace").into(),
                    Term::atom("king").into(),
                ).into(),
                ExprKind::If(
                    Term::atom("king").into(),
                    Term::atom("ace").into(),
                ).into(),
            ]).into(),
            ExprKind::Not(
                ExprKind::And(vec![
                    ExprKind::If(
                        Term::atom("ace").into(),
                        Term::atom("king").into(),
                    ).into(),
                    ExprKind::If(
                        Term::atom("king").into(),
                        Term::atom("ace").into(),
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
                                Term::atom("apple").into()
                            ).into()
                        ).into()
                    ).into()
            ).into()
        ).into();
        let normalized = ExprKind::Not(Term::atom("apple").into()).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }

    #[test]
    fn negate_normalize_1() {
        let expr: Expr = ExprKind::Not(
            ExprKind::And(vec![
                Term::atom("apple").into(),
                Term::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                Term::atom("apple").into()
            ).into(),
            ExprKind::Not(
                Term::atom("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_2() {
        let expr: Expr = ExprKind::Not(
            ExprKind::And(vec![
                Term::atom("apple").into(),
                Term::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                Term::atom("apple").into()
            ).into(),
            ExprKind::Not(
                Term::atom("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_3() {
        let expr: Expr = ExprKind::Not(
            ExprKind::Or(vec![
                Term::atom("apple").into(),
                Term::atom("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                Term::atom("apple").into(),
            ).into(),
            ExprKind::Not(
                Term::atom("banana").into(),
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }
    #[test]
    fn negate_normalize_4() {
        let expr: Expr = ExprKind::Not(
            ExprKind::Or(vec![
                Term::atom("apple").into(),
                Term::atom("banana").into(),
                ExprKind::Not(
                    ExprKind::And(vec![
                        Term::atom("coconut").into(),
                        ExprKind::Not(
                            Term::atom("dragonfruit").into(),
                        ).into()
                    ]).into()
                ).into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                Term::atom("apple").into(),
            ).into(),
            ExprKind::Not(
                Term::atom("banana").into(),
            ).into(),
            ExprKind::And(vec![
                Term::atom("coconut").into(),
                ExprKind::Not(
                    Term::atom("dragonfruit").into()
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
                        Term::atom("a").into(),
                        Term::atom("b").into(),
                    ]).into(),
                ]).into(),
                Term::atom("c").into(),
            ]).into(),
            Term::atom("d").into(),
            Term::atom("e").into(),
            ExprKind::Or(vec![
                Term::atom("f").into(),
            ]).into(),
            Term::atom("g").into(),
            ExprKind::Or(vec![
                Term::atom("h").into(),
            ]).into(),
            Term::atom("i").into(),
        ]).into();
        let normalized = ExprKind::Or(vec![
            Term::atom("a").into(),
            Term::atom("b").into(),
            Term::atom("c").into(),
            Term::atom("d").into(),
            Term::atom("e").into(),
            Term::atom("f").into(),
            Term::atom("g").into(),
            Term::atom("h").into(),
            Term::atom("i").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_6() {
        let expr: Expr = ExprKind::And(vec![
            ExprKind::And(vec![
                ExprKind::And(vec![
                    ExprKind::And(vec![
                        Term::atom("p").into(),
                    ]).into(),
                    Term::atom("q").into(),
                ]).into(),
                ExprKind::And(vec![
                    Term::atom("r").into(),
                    Term::atom("s").into(),
                    Term::atom("t").into(),
                    Term::atom("u").into(),
                ]).into(),
                ExprKind::And(vec![
                    Term::atom("v").into(),
                    Term::atom("w").into(),
                ]).into(),
            ]).into(),
            Term::atom("x").into(),
            ExprKind::And(vec![
                Term::atom("y").into(),
                Term::atom("z").into(),
            ]).into(),
        ]).into();
        let normalized = ExprKind::And(vec![
            Term::atom("p").into(),
            Term::atom("q").into(),
            Term::atom("r").into(),
            Term::atom("s").into(),
            Term::atom("t").into(),
            Term::atom("u").into(),
            Term::atom("v").into(),
            Term::atom("w").into(),
            Term::atom("x").into(),
            Term::atom("y").into(),
            Term::atom("z").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn normalize_negations_7() {
        let expr: Expr = ExprKind::Iff(
            ExprKind::Xor(
                Term::atom("a").into(),
                Term::atom("b").into(),
            ).into(),
            ExprKind::Not(
                ExprKind::Iff(
                    Term::atom("a").into(),
                    Term::atom("b").into(),
                ).into(),
            ).into(),
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Or(vec![
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        ExprKind::Not(Term::atom("a").into()).into(),
                        Term::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        Term::atom("a").into(),
                        ExprKind::Not(Term::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        Term::atom("a").into(),
                        Term::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        ExprKind::Not(Term::atom("a").into()).into(),
                        ExprKind::Not(Term::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
            ]).into(),
            ExprKind::Or(vec![
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        Term::atom("a").into(),
                        Term::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        ExprKind::Not(Term::atom("a").into()).into(),
                        ExprKind::Not(Term::atom("b").into()).into(),
                    ]).into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Or(vec![
                        ExprKind::Not(Term::atom("a").into()).into(),
                        Term::atom("b").into(),
                    ]).into(),
                    ExprKind::Or(vec![
                        Term::atom("a").into(),
                        ExprKind::Not(Term::atom("b").into()).into(),
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
                Term::atom("day").into(),
                Term::atom("night").into(),
            ]).into(),
            ExprKind::And(vec![
                Term::atom("love").into(),
                Term::atom("war").into(),
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
