use std::fmt;

fn get_tabs(f: &fmt::Formatter) -> (usize, String) {
    let width = if let Some(width) = f.width() {
        width
    } else {
        0
    };
    (width, "   ".repeat(width))
}

pub enum Expr {
    Number(u64),
    Variable(Variable),
    True,
    False,
    Op(Box<Expr>, Opcode, Box<Expr>),
    Right(Opcode, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            Expr::Number(i) => write!(f, "${:?}", i),
            Expr::Variable(v) => write!(f, "{tabs}{:width$?}", v, tabs = tabs, width = width + 1),
            Expr::True => write!(f, "$true"),
            Expr::False => write!(f, "$false"),
            Expr::Op(l, o, r) => write!(f, "({:?} of {:?} and {:?})", o, l, r,),
            Expr::Right(o, e) => write!(
                f,
                "{tabs}({:width$?} of {:width$?})",
                o,
                e,
                tabs = tabs,
                width = width + 1
            ),
            Expr::Ternary(c, t, _f) => write!(
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

#[derive(Clone)]
pub enum Type {
    Int,
    Bool,
    Str,
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Str => write!(f, "Str"),
        }
    }
}

#[derive(Clone)]
pub enum Variable {
    Single(String),
    Array(String, u64),
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Variable::Single(i) => write!(f, "(Var {:?})", i),
            Variable::Array(i, s) => write!(f, "(Arr {:?} at pos {:?})", i, s),
        }
    }
}

pub enum Decl {
    Single(String, Type, Option<Box<Expr>>),
    Array(String, Type, u64, Option<Vec<Box<Expr>>>),
    Func(String, Option<Type>, Option<Vec<FuncParam>>, Block),
}

impl fmt::Debug for Decl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            Decl::Single(i, t, Some(e)) => write!(
                f,
                "{tabs}({:width$?} of type {:width$?} with value {:width$?})",
                i,
                t,
                e,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Single(i, t, _) => write!(
                f,
                "{tabs}({:width$?} of type {:width$?})",
                i,
                t,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Array(i, t, s, Some(e)) => write!(
                f,
                "{tabs}([{:width$?}] of size {:width$?} of type {:width$?} with values {:width$?})",
                i,
                s,
                t,
                e,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Array(i, t, s, _) => write!(
                f,
                "{tabs}([{:width$?}] of size {:width$?} of type {:width$?})",
                i,
                s,
                t,
                tabs = tabs,
                width = width + 1
            ),

            Decl::Func(i, Some(t), Some(p), b) => write!(
                f,
                "{tabs}(func {:?}\n      {tabs}with params ({:?})\n      {tabs}returning ({:width$?})\n      {tabs}executing (\n{:width$?}\n   {tabs}))",
                i,
                p,
                t,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, Some(t), _, b) => write!(
                f,
                "{tabs}(func {:?} with no params\n      {tabs}returning ({:width$?})\n      {tabs}executing (\n{:width$?})\n   {tabs})",
                i,
                t,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, _, Some(p), b) => write!(
                f,
                "{tabs}(proc {:?}\n      {tabs}with params ({:?})\n      {tabs}executing (\n{:width$?})\n   {tabs})",
                i,
                p,
                b,
                tabs = tabs,
                width = width + 3
            ),

            Decl::Func(i, _, _, b) => write!(
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

pub enum FuncParam {
    Single(String, Type),
    Array(String, Type),
}

impl fmt::Debug for FuncParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (width, tabs) = get_tabs(f);
        match self {
            FuncParam::Single(i, t) => write!(
                f,
                "{tabs}(Param {:width$?}, {:width$?})",
                i,
                t,
                tabs = tabs,
                width = width + 1
            ),
            FuncParam::Array(i, t) => write!(
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
        let (width, tabs) = get_tabs(f);
        match self {
            Stmt::Attr(v, e) => write!(
                f,
                "(Attr {:?} receives {:?})",
                v,
                e,
                ),

            Stmt::Stop => write!(f, "Stop"),
            Stmt::Skip => write!(f, "Skip"),

            Stmt::Return(Some(a)) => {
                write!(f, "(Return {:?})", a)
            }
            Stmt::Return(_) => write!(f, "Return"),

            Stmt::Read(v) => write!(f, "(Read {:?})", v),
            Stmt::Write(v) => write!(f, "(Write {:?})", v),

            Stmt::Call(fun, Some(p)) => write!(
                f,
                "(Call {:width$?} with params {:?})",
                fun,
                p,
                width = width + 1
            ),
            Stmt::Call(fun, _) => {
                write!(f, "(Call {:width$?})", fun, width = width + 1)
            }

            Stmt::If(expr, b, _elif, _else) => {
                write!( f, "(If {:?} then (\n{:width$?})", expr, b, width = width + 1)?;
                if _elif.len() == 0 {
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

            Stmt::While(e, b) => write!(
                f,
                "(While {:?} do(\n{:width$?}\n{tabs}))",
                e,
                b,
                tabs = tabs,
                width = width + 1
            ),
            Stmt::For(i, t, s, b) => {
                write!(
                    f,
                    "(For\n   {tabs}with init {:?}\n   {tabs}and with test {:?}\n   {tabs}and with step {:?}\n   {tabs}then do(\n{:width$?}\n{tabs}))",
                    i, t, s, b, tabs = tabs, width = width + 2)
            }
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
        let (width, _tabs) = get_tabs(f);
        match self {
            Either::Left(a) => write!(f, "(Left {:width$?})", a, width = width + 1),
            Either::Right(b) => write!(f, "(Right {:width$?})", b, width = width + 1),
        }
    }
}

pub struct Block {
    pub decl: Vec<Decl>,
    pub commands: Vec<Either<Stmt, Block>>,
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
        if self.decl.len() == 0 {
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
        if self.commands.len() == 0 {
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
