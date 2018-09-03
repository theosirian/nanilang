use ast::*;
use llvm::core::*;
use llvm::prelude::*;

use std::collections::HashMap;
use std::ffi::*;
use std::ptr;

macro_rules! c_str {
    ($s:expr) => {{
        concat!($s, "\0").as_ptr() as *const i8
    }};
}

macro_rules! m_str {
    ($s:expr) => {{
        concat!($s, "\0").as_ptr() as *mut i8
    }};
}

macro_rules! mm_str {
    ($s:expr) => {{
        concat!($s, "\0").as_ptr() as *mut *mut i8
    }};
}

macro_rules! as_str {
    ($v:ident) => {
        CString::new($v.clone()).unwrap().as_ptr() as *const i8
    };
}

#[derive(Clone, Debug)]
enum Symbol {
    Variable(LLVMValueRef),
    Array(u32, LLVMValueRef),
    Func(String),
}

unsafe fn gen_type(context: LLVMContextRef, t: Option<Type>) -> LLVMTypeRef {
    match t {
        Some(Type::Bool) => LLVMInt1TypeInContext(context),
        Some(Type::Int) => LLVMInt64TypeInContext(context),
        Some(Type::Str) => panic!("Do not use gen_type with Strings!"),
        None => LLVMVoidTypeInContext(context),
    }
}

unsafe fn flatten_expr(
    context: LLVMContextRef,
    symbols: &HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    e: Expr,
) -> LLVMValueRef {
    let mut v = Vec::new();
    match e {
        Expr::Number(n) => {
            v.push(LLVMConstInt(gen_type(context, Some(Type::Int)), n, 1));
        }
        Expr::Variable(Variable::Single(s)) => {
            if let Some(vec) = symbols.get(&s) {
                if let Some(Symbol::Variable(mut var)) = vec.last().clone() {
                    v.push(LLVMBuildLoad(builder, var, c_str!("flat")));
                }
            }
        }
        Expr::True => {
            v.push(LLVMConstInt(gen_type(context, Some(Type::Bool)), 1, 1));
        }
        Expr::False => {
            v.push(LLVMConstInt(gen_type(context, Some(Type::Bool)), 0, 1));
        }
        Expr::Op(lhs, op, rhs) => match op {
            Opcode::Add => {
                let lhs = flatten_expr(context, symbols, builder, *lhs);
                let rhs = flatten_expr(context, symbols, builder, *rhs);
                v.push(LLVMBuildAdd(builder, lhs, rhs, c_str!("add")));
            }
            Opcode::Sub => {
                let lhs = flatten_expr(context, symbols, builder, *lhs);
                let rhs = flatten_expr(context, symbols, builder, *rhs);
                v.push(LLVMConstSub(lhs, rhs));
            }
            Opcode::Mul => {
                let lhs = flatten_expr(context, symbols, builder, *lhs);
                let rhs = flatten_expr(context, symbols, builder, *rhs);
                v.push(LLVMConstMul(lhs, rhs));
            }
            Opcode::Div => {
                let lhs = flatten_expr(context, symbols, builder, *lhs);
                let rhs = flatten_expr(context, symbols, builder, *rhs);
                v.push(LLVMConstSDiv(lhs, rhs));
            }
            _ => println!("uninplemented!"),
        },
        Expr::Right(Opcode::Negative, e) => {
            v.push(LLVMConstInt(
                gen_type(context, Some(Type::Bool)),
                -1i64 as u64,
                1,
            ));
        }
        Expr::Right(Opcode::Not, e) => {}
        Expr::Right(o, _) => {
            panic!("<{:?}> is an invalid right operator! ", o);
        }
        _ => println!("uninplemented!"),
    }
    if let Some(a) = v.last().cloned() {
        a
    } else {
        //panic!("invalid state");
        LLVMConstInt(gen_type(context, Some(Type::Int)), 42, 1)
    }
}

unsafe fn local_add_variable(
    context: LLVMContextRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    n: String,
    t: Type,
    e: Option<Box<Expr>>,
) {
    let t = gen_type(context, Some(t));
    let decl = LLVMBuildAlloca(builder, t, as_str!(n));
    if let Some(e) = e {
        let flattened = flatten_expr(context, symbols, builder, *e);
        LLVMBuildStore(builder, flattened, decl);
    }
    let new_symbol = Symbol::Variable(decl);
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

unsafe fn local_add_array(
    context: LLVMContextRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    n: String,
    t: Type,
    s: u64,
    e: Option<Vec<Box<Expr>>>,
) {
    let t = gen_type(context, Some(t));
    let array_type = LLVMArrayType(t, s as u32);
    let decl = LLVMBuildArrayAlloca(builder, array_type, LLVMConstInt(t, 0, 1), as_str!(n));
    if let Some(e) = e {
        let mut args = e
            .iter()
            .map(|b| match **b {
                Expr::Number(e) => LLVMConstInt(t, e, 1),
                _ => panic!("Cannot initialize global value with non-const expresion!"),
            })
            .collect::<Vec<_>>();
        let values = LLVMConstArray(array_type, args.as_mut_ptr(), args.len() as u32);
        LLVMBuildStore(builder, values, decl);
    }
    let new_symbol = Symbol::Array(s as u32, decl);
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

unsafe fn global_add_func(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    n: String,
    t: Option<Type>,
    a: Option<Vec<FuncParam>>,
    b: Block,
) {
    let builder = LLVMCreateBuilderInContext(context);
    let t = gen_type(context, t);
    let mut args = if let Some(a) = a {
        a.iter()
            .map(|_| gen_type(context, Some(Type::Int)))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    let function_type = LLVMFunctionType(t, args.as_mut_ptr(), args.len() as u32, 0);
    let function = LLVMAddFunction(module, as_str!(n), function_type);

    let entry = LLVMAppendBasicBlockInContext(context, function, c_str!("entry"));
    LLVMPositionBuilderAtEnd(builder, entry);

    if n == "main" {
        LLVMBuildGlobalStringPtr(builder, c_str!("%d"), c_str!("format_int"));
        LLVMBuildGlobalStringPtr(builder, c_str!("%s"), c_str!("format_str"));
        let int8_type = LLVMInt8TypeInContext(context);
        let int32_type = LLVMInt32TypeInContext(context);
        let mut printf_args = [LLVMPointerType(int8_type, 0)];
        let printf_type = LLVMFunctionType(int32_type, printf_args.as_mut_ptr(), 0, 1);
        LLVMAddFunction(module, c_str!("printf"), printf_type);
    }

    for i in b.decl {
        match i {
            Decl::Single(n, t, e) => local_add_variable(context, symbols, builder, n, t, e),
            Decl::Array(n, t, s, e) => local_add_array(context, symbols, builder, n, t, s, e),
            _ => println!("uninplemented!"),
        }
    }

    gen_block(context, module, symbols, builder, b.commands);
    //for i in b.stmt {}
    LLVMDisposeBuilder(builder);
    let new_symbol = Symbol::Func(n.clone());
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

unsafe fn gen_block(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    stmt: Vec<Either<Stmt, Block>>,
) {
    // This deep clones the Vector as far as tested.
    let mut my_symbols = symbols.clone();
    for i in stmt {
        match i {
            Either::Left(Stmt::Attr(Variable::Single(v), e)) => {
                if let Some(vec) = my_symbols.get(&v) {
                    if let Some(Symbol::Variable(mut var)) = vec.last() {
                        let flattened = flatten_expr(context, &my_symbols, builder, *e);
                        LLVMBuildStore(builder, flattened, var);
                    }
                }
            }
            Either::Left(Stmt::Write(vec)) => {
                for i in vec {
                    let flattened = flatten_expr(context, &my_symbols, builder, *i);
                    let format_str = LLVMGetNamedGlobal(module, c_str!("format_int"));
                    let mut printf_args = [format_str, flattened];
                    let printf_fn = LLVMGetNamedFunction(module, c_str!("printf"));
                    LLVMBuildCall(
                        builder,
                        printf_fn,
                        printf_args.as_mut_ptr(),
                        2,
                        c_str!("write"),
                    );
                }
            }
            Either::Left(Stmt::Return(v)) => {
                if let Some(v) = v {
                    let flattened = flatten_expr(context, &my_symbols, builder, *v);
                    LLVMBuildRet(builder, flattened);
                } else {
                    LLVMBuildRetVoid(builder);
                }
            }
            Either::Left(_) => println!("uninplemented!"),
            Either::Right(b) => {
                for i in b.decl {
                    match i {
                        Decl::Single(n, t, e) => {
                            local_add_variable(context, &mut my_symbols, builder, n, t, e)
                        }
                        Decl::Array(n, t, s, e) => {
                            local_add_array(context, &mut my_symbols, builder, n, t, s, e)
                        }
                        _ => panic!("Cannot declare functions inside functions!"),
                    }
                }
                gen_block(context, module, &mut my_symbols, builder, b.commands)
            }
        }
    }
}

unsafe fn global_add_variable(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    n: String,
    t: Type,
    e: Option<Box<Expr>>,
) {
    let t = gen_type(context, Some(t));
    let decl = LLVMAddGlobal(module, t, as_str!(n));
    if let Some(e) = e {
        let b = *e;
        if let Expr::Number(v) = b {
            LLVMSetInitializer(decl, LLVMConstInt(t, v as u64, 1));
        }
    } else {
        panic!("Cannot initialize global value with non-const expresion!");
    }
    let new_symbol = Symbol::Variable(decl);
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

unsafe fn global_add_array(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    n: String,
    t: Type,
    s: u64,
    e: Option<Vec<Box<Expr>>>,
) {
    let t = gen_type(context, Some(t));
    let array_type = LLVMArrayType(t, s as u32);
    let decl = LLVMAddGlobal(module, array_type, as_str!(n));
    if let Some(e) = e {
        let mut args = e
            .iter()
            .map(|b| match **b {
                Expr::Number(e) => LLVMConstInt(t, e, 0),
                _ => panic!("Cannot initialize global value with non-const expresion!"),
            })
            .collect::<Vec<_>>();
        let values = LLVMConstArray(array_type, args.as_mut_ptr(), args.len() as u32);
        LLVMSetInitializer(decl, values);
    }
    let new_symbol = Symbol::Array(s as u32, decl);
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

pub unsafe fn gen(decls: Vec<Decl>) {
    let context = LLVMContextCreate();
    let module = LLVMModuleCreateWithNameInContext(c_str!("program"), context);
    let mut symbols: HashMap<String, Vec<Symbol>> = HashMap::new();
    for i in decls {
        match i {
            Decl::Single(n, t, e) => global_add_variable(context, module, &mut symbols, n, t, e),
            Decl::Array(n, t, s, e) => global_add_array(context, module, &mut symbols, n, t, s, e),
            Decl::Func(n, t, a, b) => global_add_func(context, module, &mut symbols, n, t, a, b),
        }
    }
    LLVMDumpModule(module);
    LLVMPrintModuleToFile(module, c_str!("test.ll"), mm_str!("idk"));
    LLVMContextDispose(context);
}
