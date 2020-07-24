#[macro_use]
mod error;
#[macro_use]
mod prover;
mod ast;

extern crate pretty_env_logger;
#[macro_use] extern crate log;

#[inline]
pub fn fibonacci(n: u64) -> u64 {
    let mut a = 0;
    let mut b = 1;
    match n {
        0 => b,
        _ => {
            for _ in 0..n {
                let sum = a + b;
                a = b;
                b = sum;
            }
            b
        }
    }
}

