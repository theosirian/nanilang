pub mod ast;
pub mod calculator;

fn main() {
    let expr = calculator::ExprParser::new().parse("22 * 44 + 66").unwrap();
    println!("{:?}", expr);
    let expr = calculator::ExprParser::new()
        .parse("12 == 2 && -12")
        .unwrap();
    println!("{:?}", expr);
    let expr = calculator::ExprParser::new()
        .parse("12 == true ? 0 : 1 + 2")
        .unwrap();
    println!("{:?}", expr);
    let expr = calculator::ExprParser::new()
        .parse("12 == true ? (13 == false ? 0 : 1) : 1 + 2")
        .unwrap();
    println!("{:?}", expr);
}
