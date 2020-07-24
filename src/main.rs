#[macro_use]
mod error;
#[macro_use]
mod prover;
mod ast;
mod client;

extern crate pretty_env_logger;
#[macro_use] extern crate log;

fn main() -> Result<(), ()> {
    pretty_env_logger::init();

    if let Err(why) = client::start() {
        eprintln!("{}", why);
    };

    Ok( () )
}


