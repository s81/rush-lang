mod ast;
mod borrowck;
mod cgen;
mod derive;
mod diag;
mod driver;
mod lexer;
mod mir;
mod mono;
mod ownck;
mod parser;
mod types;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    std::process::exit(driver::main(args));
}
