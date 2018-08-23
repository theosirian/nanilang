pub mod ast;
pub mod calculator;

fn main() {
    let expr = calculator::ExprParser::new().parse("22 * 44 + 66").unwrap();
    println!("{:?}", expr);
}
