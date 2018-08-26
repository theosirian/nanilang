mod ast;
mod grammar;

fn main() {
    let expr = grammar::ExprParser::new().parse("22 * 44 + 66").unwrap();
    println!("{:?}", expr);
    let expr = grammar::ExprParser::new().parse("12 == 2 && -12").unwrap();
    println!("{:?}", expr);
    let expr = grammar::ExprParser::new()
        .parse("12 == true ? __testing : 1 + 2")
        .unwrap();
    println!("{:?}", expr);
    let expr = grammar::ExprParser::new()
        .parse("12 == true ? (13 == hello ? 0 : 1) : 1 + 2")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::DeclParser::new().parse("let x: bool;").unwrap();
    println!("{:?}", expr);
    let expr = grammar::DeclParser::new().parse("let x, y: str;").unwrap();
    println!("{:?}", expr);
    let expr = grammar::DeclParser::new()
        .parse("let x, y = true: bool;")
        .unwrap();
    println!("{:?}", expr);
    let expr = grammar::DeclParser::new()
        .parse("let x, y = 0 + x, z = 2: int;")
        .unwrap();
    println!("{:?}", expr);
}
