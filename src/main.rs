
#[macro_use]
mod prover;
mod ast;

fn main() {
    let source = "andy";
    let expr = match ast::parse(source) {
        Ok(expr) => expr,
        Err(why) => {
            eprintln!("{}", why);
            return;
        }
    };
    println!("{:?}", expr);

}
