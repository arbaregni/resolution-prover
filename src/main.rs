
#[macro_use]
mod prover;
mod ast;

fn main() {
    let source = "not not not andy";
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

}
