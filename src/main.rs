
#[macro_use]
mod prover;
mod ast;

fn main() {
    let source = "(me and you) or (us and them)";
    let expr = match ast::parse(source) {
        Ok(expr) => expr,
        Err(why) => {
            eprintln!("{}", why);
            return;
        }
    };
    println!("{:?}", expr);

    let expr = expr.normalize_negations();

    println!("normalized: {:#?}", expr);

    let expr = expr.distribute_ors_inward();

    println!("in cnf: {:#?}", expr);

}
