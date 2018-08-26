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
    let expr = grammar::DeclParser::new()
        .parse("let x[2], y[3] = { 1, 2, 3 }: int; let x = 2: int;")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::CommandsParser::new()
        .parse("a += b + 2; b -= 2; c *= 3; d /= 4; e %= 5; a[0] += 1;")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::CommandsParser::new().parse("skip; stop;").unwrap();
    println!("{:?}", expr);

    let expr = grammar::CommandsParser::new()
        .parse("return; return 4; return a; return a[0];")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::CommandsParser::new()
        .parse("read a; read a[0]; write 10; write a; write a, b[0];")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::CommandsParser::new()
        .parse("hello(); hello(12); hello(12, 13);")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let a = 0: int; hello(a); }")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let a = true: bool; if (a) { let b = 0: int; hello(b); } }")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let a = true: bool; if (a) { let b = 0: int; hello(b); } else { hello(a); } }")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let a = true: bool; let b = 0: int; if (a) { let b = 0: int; hello(b); } else if (b > 3) { hello(false); } else { hello(a); } }")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let i = 2: int; while (true) { hello(i); } }")
        .unwrap();
    println!("{:?}", expr);

    let expr = grammar::BlockParser::new()
        .parse("{ let i: int; for (i = 0; i < 10; i += 1) { hello(i); } }")
        .unwrap();
    println!("{:?}", expr);
}
