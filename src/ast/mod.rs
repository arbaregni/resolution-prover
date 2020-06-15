mod expr;
pub use expr::*;

#[allow(dead_code)]
mod parse;
pub use parse::*;


#[cfg(test)]
mod tests {
    use crate::ast::{ExprKind, parse};
    use crate::prover::ClauseInterner;
    use indexmap::set::IndexSet;

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
    fn parse_simple_4() {
        let source = "not pleasant";
        let expr = parse(source).expect("should not error");
        assert_eq!(expr, ExprKind::Not(
            ExprKind::Literal("pleasant").into()
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

    #[test]
    fn negate_normalize_0() {
        let expr =
            ExprKind::Not(
                ExprKind::Not(
                    ExprKind::Not(
                        ExprKind::Not(
                            ExprKind::Not(
                                ExprKind::Literal("apple").into()
                            ).into()
                        ).into()
                    ).into()
            ).into()
        ).into();
        let normalized = ExprKind::Not(ExprKind::Literal("apple").into()).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }

    #[test]
    fn negate_normalize_1() {
        let expr = ExprKind::Not(
            ExprKind::And(vec![
                ExprKind::Literal("apple").into(),
                ExprKind::Literal("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                ExprKind::Literal("apple").into()
            ).into(),
            ExprKind::Not(
                ExprKind::Literal("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_2() {
        let expr = ExprKind::Not(
            ExprKind::And(vec![
                ExprKind::Literal("apple").into(),
                ExprKind::Literal("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Not(
                ExprKind::Literal("apple").into()
            ).into(),
            ExprKind::Not(
                ExprKind::Literal("banana").into()
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_3() {
        let expr = ExprKind::Not(
            ExprKind::Or(vec![
                ExprKind::Literal("apple").into(),
                ExprKind::Literal("banana").into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                ExprKind::Literal("apple").into(),
            ).into(),
            ExprKind::Not(
                ExprKind::Literal("banana").into(),
            ).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }
    #[test]
    fn negate_normalize_4() {
        let expr = ExprKind::Not(
            ExprKind::Or(vec![
                ExprKind::Literal("apple").into(),
                ExprKind::Literal("banana").into(),
                ExprKind::Not(
                    ExprKind::And(vec![
                        ExprKind::Literal("coconut").into(),
                        ExprKind::Not(
                            ExprKind::Literal("dragonfruit").into(),
                        ).into()
                    ]).into()
                ).into(),
            ]).into()
        ).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Not(
                ExprKind::Literal("apple").into(),
            ).into(),
            ExprKind::Not(
                ExprKind::Literal("banana").into(),
            ).into(),
            ExprKind::And(vec![
                ExprKind::Literal("coconut").into(),
                ExprKind::Not(
                    ExprKind::Literal("dragonfruit").into()
                ).into()
            ]).into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized)
    }
    #[test]
    fn negate_normalize_5() {
        let expr = ExprKind::Or(vec![
            ExprKind::Or(vec![
                ExprKind::Or(vec![
                    ExprKind::Or(vec![
                        ExprKind::Literal("a").into(),
                        ExprKind::Literal("b").into(),
                    ]).into(),
                ]).into(),
                ExprKind::Literal("c").into(),
            ]).into(),
            ExprKind::Literal("d").into(),
            ExprKind::Literal("e").into(),
            ExprKind::Or(vec![
                ExprKind::Literal("f").into(),
            ]).into(),
            ExprKind::Literal("g").into(),
            ExprKind::Or(vec![
                ExprKind::Literal("h").into(),
            ]).into(),
            ExprKind::Literal("i").into(),
        ]).into();
        let normalized = ExprKind::Or(vec![
            ExprKind::Literal("a").into(),
            ExprKind::Literal("b").into(),
            ExprKind::Literal("c").into(),
            ExprKind::Literal("d").into(),
            ExprKind::Literal("e").into(),
            ExprKind::Literal("f").into(),
            ExprKind::Literal("g").into(),
            ExprKind::Literal("h").into(),
            ExprKind::Literal("i").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }
    #[test]
    fn negate_normalize_6() {
        let expr = ExprKind::And(vec![
            ExprKind::And(vec![
                ExprKind::And(vec![
                    ExprKind::And(vec![
                        ExprKind::Literal("p").into(),
                    ]).into(),
                    ExprKind::Literal("q").into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Literal("r").into(),
                    ExprKind::Literal("s").into(),
                    ExprKind::Literal("t").into(),
                    ExprKind::Literal("u").into(),
                ]).into(),
                ExprKind::And(vec![
                    ExprKind::Literal("v").into(),
                    ExprKind::Literal("w").into(),
                ]).into(),
            ]).into(),
            ExprKind::Literal("x").into(),
            ExprKind::And(vec![
                ExprKind::Literal("y").into(),
                ExprKind::Literal("z").into(),
            ]).into(),
        ]).into();
        let normalized = ExprKind::And(vec![
            ExprKind::Literal("p").into(),
            ExprKind::Literal("q").into(),
            ExprKind::Literal("r").into(),
            ExprKind::Literal("s").into(),
            ExprKind::Literal("t").into(),
            ExprKind::Literal("u").into(),
            ExprKind::Literal("v").into(),
            ExprKind::Literal("w").into(),
            ExprKind::Literal("x").into(),
            ExprKind::Literal("y").into(),
            ExprKind::Literal("z").into(),
        ]).into();
        assert_eq!(expr.normalize_negations(), normalized);
    }

    #[test]
    fn to_clauses_0() {
        let expr = ExprKind::Or(vec![
            ExprKind::And(vec![
                ExprKind::Literal("day").into(),
                ExprKind::Literal("night").into(),
            ]).into(),
            ExprKind::And(vec![
                ExprKind::Literal("love").into(),
                ExprKind::Literal("war").into(),
            ]).into()
        ]).into();
        // (day and night) or (love and war)
        // (day or (love and war)) and (night or (love and war))
        // (day or love) and (day or war) and (night or love) and (night or war)
        let mut interner = ClauseInterner::new();
        let mut clause_set_expected = IndexSet::new();
        interner.intern_and_insert(&mut clause_set_expected, clause!(day, love));
        interner.intern_and_insert(&mut clause_set_expected, clause!(day, war));
        interner.intern_and_insert(&mut clause_set_expected, clause!(night, love));
        interner.intern_and_insert(&mut clause_set_expected, clause!(night, war));

        let mut clause_set_actual = IndexSet::new();
        expr.into_clauses(&mut clause_set_actual, &mut interner);

        assert_eq!(clause_set_actual, clause_set_expected);
    }
}
