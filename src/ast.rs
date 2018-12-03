use llvm::LLVMIntPredicate;
use std::fmt;

use codespan::{ByteIndex, Span};

pub type Location = Span<ByteIndex>;

#[macro_export]
macro_rules! flatten {
    ($v:ident) => {
        let mut __aux = Vec::new();
        for i in $v {
            let mut i = i;
            __aux.append(&mut i);
        }
        let $v = __aux;
    };
}

fn get_tabs(f: &fmt::Formatter) -> (usize, String) {
    let width = if let Some(width) = f.width() {
        width
    } else {
        0
    };
    (width, "   ".repeat(width))
}

#[derive(Clone, PartialEq)]
pub enum Expr {
    Number(u64, Location),
    Variable(Variable, Location),
    True(Location),
    False(Location),
    Call(String, Option<Vec<Box<Expr>>>, Location),
    Op(Box<Expr>, Opcode, Box<Expr>, Location),
    Right(Opcode, Box<Expr>, Location),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>, Location),
}

#[derive(Clone, PartialEq)]
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

#[derive(Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Str,
    Void,
    Agg(Box<Type>),
}

impl Default for Type {
    fn default() -> Type {
        Type::Void
    }
}

#[derive(Clone, PartialEq)]
pub enum Variable {
    Single(String, Location),
    Array(String, Box<Expr>, Location),
}

#[derive(Clone, PartialEq)]
pub enum Decl {
    Single(String, Type, Option<Box<Expr>>, Location),
    Array(String, Type, u64, Option<Vec<Box<Expr>>>, Location),
    Func(
        String,
        Option<Type>,
        Option<Vec<FuncParam>>,
        Block,
        Location,
    ),
}

#[derive(Clone, PartialEq)]
pub enum FuncParam {
    Single(String, Type, Location),
    Array(String, Type, Location),
}

#[derive(Clone, PartialEq)]
pub enum Stmt {
    Attr(Variable, Box<Expr>, Location),
    Stop(Location),
    Skip(Location),
    Return(Option<Box<Expr>>, Location),
    Read(Variable, Location),
    Write(Vec<Box<Expr>>, Location),
    Call(String, Option<Vec<Box<Expr>>>, Location),
    If(
        Box<Expr>,
        Block,
        Vec<(Box<Expr>, Block)>,
        Option<Block>,
        Location,
    ),
    While(Box<Expr>, Block, Location),
    For(Box<Stmt>, Box<Expr>, Box<Stmt>, Block, Location),
}

#[derive(Clone, PartialEq)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

#[derive(Clone, PartialEq)]
pub struct Block {
    pub decl: Vec<Decl>,
    pub commands: Vec<Either<Stmt, Block>>,
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            Expr::Number(i, _) => write!(f, "${:?}", i),
            Expr::Variable(v, _) => {
                write!(f, "{tabs}{:width$?}", v, tabs = tabs, width = width + 1)
            }
            Expr::True(_) => write!(f, "$true"),
            Expr::False(_) => write!(f, "$false"),

            Expr::Call(fun, Some(p), _) => write!(
                f,
                "(Call {:width$?} with params {:?})",
                fun,
                p,
                width = width + 1
            ),
            Expr::Call(fun, _, _) => {
                write!(f, "(Call {:width$?})", fun, width = width + 1)
            }

            Expr::Op(l, o, r, _) => {
                write!(f, "({:?} of {:?} and {:?})", o, l, r,)
            }
            Expr::Right(o, e, _) => write!(
                f,
                "{tabs}({:width$?} of {:width$?})",
                o,
                e,
                tabs = tabs,
                width = width + 1
            ),
            Expr::Ternary(c, t, _f, _) => write!(
                f,
                "{tabs}(If {:?} Then {:?} Else {:?})",
                c,
                t,
                _f,
                tabs = tabs,
            ),
        }
    }
}

impl Opcode {
    pub fn pred(&self) -> LLVMIntPredicate {
        match self {
            Opcode::Lesser => LLVMIntPredicate::LLVMIntSLT,
            Opcode::LesserOrEqual => LLVMIntPredicate::LLVMIntSLE,
            Opcode::Greater => LLVMIntPredicate::LLVMIntSGT,
            Opcode::GreaterOrEqual => LLVMIntPredicate::LLVMIntSGE,
            Opcode::Equal => LLVMIntPredicate::LLVMIntEQ,
            Opcode::Different => LLVMIntPredicate::LLVMIntNE,
            _ => panic!("Opcode does not have intpredicate!"),
        }
    }
}

impl fmt::Debug for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Opcode::Negative => write!(f, "-"),
            Opcode::Not => write!(f, "!"),
            Opcode::Mul => write!(f, "*"),
            Opcode::Div => write!(f, "/"),
            Opcode::Mod => write!(f, "%"),
            Opcode::Add => write!(f, "+"),
            Opcode::Sub => write!(f, "-"),
            Opcode::Lesser => write!(f, "<"),
            Opcode::LesserOrEqual => write!(f, "<="),
            Opcode::Greater => write!(f, ">"),
            Opcode::GreaterOrEqual => write!(f, ">="),
            Opcode::Equal => write!(f, "=="),
            Opcode::Different => write!(f, "!="),
            Opcode::And => write!(f, "&&"),
            Opcode::Or => write!(f, "||"),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Str => write!(f, "Str"),
            Type::Void => write!(f, "Void"),
            Type::Agg(type_of) => write!(f, "Agg({:?})", *type_of),
        }
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Variable::Single(i, _) => write!(f, "(Var {:?})", i),
            Variable::Array(i, s, _) => {
                write!(f, "(Arr {:?} at pos {:?})", i, s)
            }
        }
    }
}

impl fmt::Debug for Decl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            Decl::Single(i, t, Some(e), _) => write!(
                f,
                "{tabs}({:width$?} of type {:width$?} with value {:width$?})",
                i,
                t,
                e,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Single(i, t, _, _) => write!(
                f,
                "{tabs}({:width$?} of type {:width$?})",
                i,
                t,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Array(i, t, s, Some(e), _) => write!(
                f,
                "{tabs}([{:width$?}] of size {:width$?} of type {:width$?} with values {:width$?})",
                i,
                s,
                t,
                e,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Array(i, t, s, _, _) => write!(
                f,
                "{tabs}([{:width$?}] of size {:width$?} of type {:width$?})",
                i,
                s,
                t,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Func(i, Some(t), Some(p), b, _) => write!(
                f,
                "{tabs}(func {:?}\n      {tabs}with params ({:?})\n      {tabs}returning ({:width$?})\n      {tabs}executing (\n{:width$?}\n   {tabs}))",
                i,
                p,
                t,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, Some(t), _, b, _) => write!(
                f,
                "{tabs}(func {:?} with no params\n      {tabs}returning ({:width$?})\n      {tabs}executing (\n{:width$?})\n   {tabs})",
                i,
                t,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, _, Some(p), b, _) => write!(
                f,
                "{tabs}(proc {:?}\n      {tabs}with params ({:?})\n      {tabs}executing (\n{:width$?})\n   {tabs})",
                i,
                p,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, _, _, b, _) => write!(
                f,
                "{tabs}(proc {:?} with no params executing (\n{:width$?})\n   {tabs})",
                i,
                b,
                tabs = tabs,
                width = width + 3
            ),
        }
    }
}

impl fmt::Debug for FuncParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            FuncParam::Single(i, t, _) => write!(
                f,
                "{tabs}(Param {:width$?}, {:width$?})",
                i,
                t,
                tabs = tabs,
                width = width + 1
            ),
            FuncParam::Array(i, t, _) => write!(
                f,
                "{tabs}(Param {:width$?}[], {:width$?})",
                i,
                t,
                tabs = tabs,
                width = width + 1
            ),
        }
    }
}

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            Stmt::Attr(v, e, _) => write!(
                f,
                "(Attr {:?} receives {:?})",
                v,
                e,
                ),

            Stmt::Stop(_) => write!(f, "Stop"),
            Stmt::Skip(_) => write!(f, "Skip"),

            Stmt::Return(Some(a), _) => {
                write!(f, "(Return {:?})", a)
            }
            Stmt::Return(_, _) => write!(f, "Return"),

            Stmt::Read(v, _) => write!(f, "(Read {:?})", v),
            Stmt::Write(v, _) => write!(f, "(Write {:?})", v),

            Stmt::Call(fun, Some(p), _) => write!(
                f,
                "(Call {:width$?} with params {:?})",
                fun,
                p,
                width = width + 1
            ),
            Stmt::Call(fun, _, _) => {
                write!(f, "(Call {:width$?})", fun, width = width + 1)
            }

            Stmt::If(expr, b, _elif, _else, _) => {
                write!( f, "(If {:?} then (\n{:width$?})", expr, b, width = width + 1)?;
                if _elif.is_empty() {
                    write!(f, " no elseifs")?;
                } else {
                    write!(f, " elseifs [")?;
                    for i in _elif {
                        write!(f, "\n      {tabs}(Elseif {:?} then (", i.0, tabs = tabs)?;
                        write!(f, "\n{:width$?}),", i.1, width = width + 3)?;
                    }
                    write!(f, "\n   {tabs}]", tabs = tabs)?;
                }
                if let Some(_else) = _else {
                    write!(f, " else (\n{:width$?}\n   {tabs}))", _else, tabs = tabs, width = width + 2)
                } else {
                    write!(f, " no else)")
                }
            },

            Stmt::While(e, b, _) => write!(
                f,
                "(While {:?} do(\n{:width$?}\n{tabs}))",
                e,
                b,
                tabs = tabs,
                width = width + 1
            ),
            Stmt::For(i, t, s, b, _) => {
                write!(
                    f,
                    "(For\n   {tabs}with init {:?}\n   {tabs}and with test {:?}\n   {tabs}and with step {:?}\n   {tabs}then do(\n{:width$?}\n{tabs}))",
                    i, t, s, b, tabs = tabs, width = width + 2)
            }
        }
    }
}

impl<A, B> fmt::Debug for Either<A, B>
where
    A: fmt::Debug,
    B: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, _tabs) = get_tabs(f);
        match self {
            Either::Left(a) => {
                write!(f, "(Left {:width$?})", a, width = width + 1)
            }
            Either::Right(b) => {
                write!(f, "(Right {:width$?})", b, width = width + 1)
            }
        }
    }
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
        let (width, tabs) = get_tabs(f);
        write!(f, "{tabs}(Block", tabs = tabs)?;
        if self.decl.is_empty() {
            write!(f, "\n   {tabs}with no decls", tabs = tabs)?;
        } else {
            write!(f, "\n   {tabs}with decls [", tabs = tabs)?;
            for i in &self.decl {
                write!(
                    f,
                    "\n   {tabs}{:width$?}, ",
                    i,
                    tabs = tabs,
                    width = width + 1
                )?;
            }
            write!(f, "\n   {tabs}]", tabs = tabs)?;
        }
        if self.commands.is_empty() {
            write!(f, " and with no commands\n{tabs})", tabs = tabs)
        } else {
            write!(f, " and with commands [")?;
            for i in &self.commands {
                write!(
                    f,
                    "\n      {tabs}{:width$?}, ",
                    i,
                    tabs = tabs,
                    width = width + 1
                )?;
            }
            write!(f, "\n   {tabs}]\n{tabs})", tabs = tabs)
        }
    }
}
