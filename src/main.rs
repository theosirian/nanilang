mod ast;
mod grammar;

fn main() {
    let expr = grammar::ProgramParser::new()
        .parse(
            r#"
def hello(a, b: int): int {
    let a = 0: int;
    read a;
    write a;
}

let global = 13: int;

def hi() {
    write 12;
}

def main(): int {
    let i: int;
    let a = true: bool;
    let b = 0: int;
    let c[2] = {0, 1}: int;

    let x: bool;
    let y, z: str;
    let w, d = true: bool;
    let e, f = 0 + e, g = 2: int;
    let h[2], i[3] = { 1, 2, 3 }: int;
    let __testing = 1: int;

    e = 22 * 44 + 66;
    f = x == true ? __testing : 1 + 2;
    g = w == true ? (13 == __testing ? 0 : 1) : 1 + 2;

    a += b + 2;
    b -= 2;
    c[0] += 1;
    e *= 3;
    f /= 4;
    g %= 5;

    read a;
    read c[0];
    write 10;
    write a;
    write a, c[0];

    hello();
    hello(a);
    hello(a, b);

    if (a) {
        let b = 0: int;
        hello(b);
    } else if (b > 3) {
        hello(false);
    } else {
        hello(a);
    }

    while (true) {
        hello(i);
        skip;
    }

    for (i = 0; i < 10; i += 1) {
        hello(i);
        stop;
    }

    return;
    return 1;
    return a;
}
        "#,
        )
        .unwrap();
    println!("{:#?}", expr);
}
