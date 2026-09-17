mod ast;
mod cgen;
mod diag;
mod driver;
mod lexer;
mod mir;
mod mono;
mod parser;
mod types;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    std::process::exit(driver::main(args));
}
