#[derive(Debug)]
pub enum Expr {
    Number(i32),
    Id(String),
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

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
    Str,
}

#[derive(Debug)]
pub enum Decl {
    Single(String, Type, Option<Box<Expr>>),
    Array(String, Type, i32, Option<Vec<Box<Expr>>>),
}
