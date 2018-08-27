use std::fmt;

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
    Func(String, Option<Type>, Vec<FuncParam>, Block),
}

#[derive(Debug)]
pub enum FuncParam {
    Single(String, Type),
    Array(String, Type),
}

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

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Attr(v, e) => write!(f, "Attr({:?}, {:?})", v, e),

            Stmt::Stop => write!(f, "Stop"),
            Stmt::Skip => write!(f, "Skip"),

            Stmt::Return(Some(a)) => write!(f, "Return({:?})", a),
            Stmt::Return(_) => write!(f, "Return"),

            Stmt::Read(v) => write!(f, "Read({:?})", v),
            Stmt::Write(v) => write!(f, "Write({:?})", v),

            Stmt::Call(fun, Some(p)) => write!(f, "Call({:?} with {:?})", fun, p),
            Stmt::Call(fun, _) => write!(f, "Call({:?})", fun),

            Stmt::If(expr, b, _elif, _else) => write!(
                f,
                "If({:?}, Then({:?}), Elifs({:?}) Else({:?}))",
                expr, b, _elif, _else
            ),
            Stmt::While(e, b) => write!(f, "While({:?}, Do({:?}))", e, b),
            Stmt::For(i, t, s, b) => write!(
                f,
                "For(Init({:?}), Test({:?}), Step({:?}), Do({:?}))",
                i, t, s, b
            ),
        }
    }
}

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A, B> fmt::Debug for Either<A, B>
where
    A: fmt::Debug,
    B: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Either::Left(a) => write!(f, "L({:?})", a),
            Either::Right(a) => write!(f, "R({:?})", a),
        }
    }
}

pub struct Block {
    decl: Vec<Decl>,
    commands: Vec<Either<Stmt, Block>>,
}

impl Block {
    pub fn new(d: Vec<Decl>, c: Vec<Either<Stmt, Block>>) -> Block {
        Block {
            decl: d,
            commands: c,
        }
    }
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Block {{\n\tdecl: [\n")?;
        for i in &self.decl {
            write!(f, "\t\t{:1?}\n", i)?;
        }
        write!(f, "\t],\n\tcommands: [\n")?;
        for i in &self.commands {
            write!(f, "\t\t{:1?}\n", i)?;
        }
        write!(f, "\t]\n}}\n")
    }
}
