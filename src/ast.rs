#[derive(Debug)]
pub enum Expr {
    Number(i32),
    Variable(Variable),
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

#[derive(Debug, Clone)]
pub enum Variable {
    Id(String),
    Array(String, i32),
}

#[derive(Debug)]
pub enum Decl {
    Single(String, Type, Option<Box<Expr>>),
    Array(String, Type, i32, Option<Vec<Box<Expr>>>),
}

#[derive(Debug)]
pub enum Stmt {
    Attr(Variable, Box<Expr>),
    Stop,
    Skip,
    Return(Option<Box<Expr>>),
    Read(Variable),
    Write(Vec<Box<Expr>>),
    Call(String, Option<Vec<Box<Expr>>>),
    If(Box<Expr>, Block, Vec<(Box<Expr>, Block)>, Option<Block>),
    While(Box<Expr>, Block),
    For(Box<Stmt>, Box<Expr>, Box<Stmt>, Block),
}

#[derive(Debug)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

#[derive(Debug)]
pub struct Block {
    decl: Option<Vec<Decl>>,
    commands: Option<Vec<Either<Stmt, Block>>>,
}

impl Block {
    pub fn new(d: Option<Vec<Decl>>, c: Option<Vec<Either<Stmt, Block>>>) -> Block {
        Block {
            decl: d,
            commands: c,
        }
    }
}
