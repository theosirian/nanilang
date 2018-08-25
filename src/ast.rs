#[derive(Debug)]
pub enum Expr {
    Number(i32),
    True,
    False,
    Op(Box<Expr>, Opcode, Box<Expr>),
    Right(Opcode, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum Opcode {
    Negative,

    Not,

    Mul,
    Div,
    Mod,

    Add,
    Sub,

    Lesser,
    LesserOrEqual,

    Greater,
    GreaterOrEqual,

    Equal,
    Different,

    And,

    Or,
}

pub enum Type {
    Int,
    Bool,
    Str,
    Array,
}
