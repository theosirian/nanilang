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
    module: LLVMModuleRef,
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
                } else {
                    panic!("Variable <{:?}> is used but not declared!", s);
                }
            } else {
                panic!("Variable <{:?}> is used but not declared!", s);
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
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildAdd(builder, lhs, rhs, c_str!("add")));
            }
            Opcode::Sub => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildSub(builder, lhs, rhs, c_str!("sub")));
            }
            Opcode::Mul => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildMul(builder, lhs, rhs, c_str!("mul")));
            }
            Opcode::Div => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildSDiv(builder, lhs, rhs, c_str!("sdiv")));
            }
            Opcode::Mod => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildSRem(builder, lhs, rhs, c_str!("srem")));
            }
            Opcode::Lesser
            | Opcode::LesserOrEqual
            | Opcode::Greater
            | Opcode::GreaterOrEqual
            | Opcode::Equal
            | Opcode::Different => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildICmp(builder, op.pred(), lhs, rhs, c_str!("cmp")));
            }
            Opcode::And => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildAnd(builder, lhs, rhs, c_str!("and")));
            }
            Opcode::Or => {
                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
                v.push(LLVMBuildOr(builder, lhs, rhs, c_str!("or")));
            }
            _ => panic!("IMPOSSIBURU! Opcode<{:?}> is unary!", op),
        },
        Expr::Call(n, None) => {
            let called_fn = LLVMGetNamedFunction(module, as_str!(n));
            let mut args = [];
            v.push(LLVMBuildCall(
                builder,
                called_fn,
                args.as_mut_ptr(),
                0,
                c_str!("fn_call"),
            ));
        }
        Expr::Right(Opcode::Negative, rhs) => {
            let rhs = flatten_expr(context, module, symbols, builder, *rhs);
            v.push(LLVMBuildMul(
                builder,
                LLVMConstInt(gen_type(context, Some(Type::Int)), -1i64 as u64, 1),
                rhs,
                c_str!("neg"),
            ));
        }
        Expr::Right(Opcode::Not, rhs) => {
            let rhs = flatten_expr(context, module, symbols, builder, *rhs);
            v.push(LLVMBuildNot(builder, rhs, c_str!("not")));
        }
        Expr::Right(o, _) => {
            panic!("IMPOSSIBURU! Opcode<{:?}> is binary!", o);
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
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    n: String,
    t: Type,
    e: Option<Box<Expr>>,
) {
    let t = gen_type(context, Some(t));
    let decl = LLVMBuildAlloca(builder, t, as_str!(n));
    if let Some(e) = e {
        let flattened = flatten_expr(context, module, symbols, builder, *e);
        LLVMBuildStore(builder, flattened, decl);
    }
    let new_symbol = Symbol::Variable(decl);
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}

unsafe fn local_add_array(
    context: LLVMContextRef,
    module: LLVMModuleRef,
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

    let test = LLVMGetNamedFunction(module, c_str!("printf"));
    // Stupid way of checking if the function is already defined.
    let against = ptr::null::<LLVMValueRef>() as *mut _;
    if test == against {
        LLVMBuildGlobalStringPtr(builder, c_str!("%d"), c_str!("format_int"));
        LLVMBuildGlobalStringPtr(builder, c_str!("%s"), c_str!("format_str"));

        let int8_type = LLVMInt8TypeInContext(context);
        let int32_type = LLVMInt32TypeInContext(context);
        let mut args = [LLVMPointerType(int8_type, 0)];
        let fn_type = LLVMFunctionType(int32_type, args.as_mut_ptr(), 0, 1);

        LLVMAddFunction(module, c_str!("printf"), fn_type);
        LLVMAddFunction(module, c_str!("scanf"), fn_type);
    }

    gen_decl(context, module, symbols, builder, function, b.decl, false);
    gen_block(context, module, symbols, builder, function, b.commands);

    LLVMDisposeBuilder(builder);
    let new_symbol = Symbol::Func(n.clone());
    symbols.entry(n).or_insert(Vec::new()).push(new_symbol);
}
unsafe fn gen_decl(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    parent: LLVMValueRef,
    decl: Vec<Decl>,
    allow_fn: bool,
) {
    for i in decl {
        match i {
            Decl::Single(n, t, e) => local_add_variable(context, module, symbols, builder, n, t, e),
            Decl::Array(n, t, s, e) => {
                local_add_array(context, module, symbols, builder, n, t, s, e)
            }
            Decl::Func(_, _, _, _) => {
                if allow_fn {
                    println!("unimplemented");
                } else {
                    panic!("Functions are not allowed here!");
                }
            }
        }
    }
}

unsafe fn build_attr(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    v: String,
    e: Expr,
) -> Result<(), String> {
    if let Some(vec) = symbols.get(&v) {
        if let Some(Symbol::Variable(mut var)) = vec.last() {
            let flattened = flatten_expr(context, module, &symbols, builder, e);
            LLVMBuildStore(builder, flattened, var);
            Ok(())
        } else {
            Err(format!("Variable <{:?}> is used but not declared!", v))
        }
    } else {
        Err(format!("Variable <{:?}> is used but not declared!", v))
    }
}

unsafe fn gen_block(
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: &mut HashMap<String, Vec<Symbol>>,
    builder: LLVMBuilderRef,
    parent: LLVMValueRef,
    looping, Option<(LLVMBasicBlockRef, LLVMBasicBlockRef)><
    stmts: Vec<Either<Stmt, Block>>,
) {
    // This deep clones the Vector as far as tested.
    let mut my_symbols = symbols.clone();
    for i in stmts {
        match i {
            Either::Left(Stmt::Attr(Variable::Single(v), e)) => {
                if let Err(s) = build_attr(context, module, &my_symbols, builder, v, *e) {
                    panic!(s);
                }
            }
            Either::Left(Stmt::Write(vec)) => {
                for i in vec {
                    let flattened = flatten_expr(context, module, &my_symbols, builder, *i);
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
            Either::Left(Stmt::Read(Variable::Single(v))) => {
                if let Some(vec) = my_symbols.get(&v) {
                    if let Some(Symbol::Variable(mut var)) = vec.last() {
                        let format_str = LLVMGetNamedGlobal(module, c_str!("format_int"));
                        let mut scanf_args = [format_str, var];
                        let scanf_fn = LLVMGetNamedFunction(module, c_str!("scanf"));
                        LLVMBuildCall(
                            builder,
                            scanf_fn,
                            scanf_args.as_mut_ptr(),
                            2,
                            c_str!("read"),
                        );
                    }
                }
            }
            Either::Left(Stmt::Return(v)) => {
                if let Some(v) = v {
                    let flattened = flatten_expr(context, module, &my_symbols, builder, *v);
                    LLVMBuildRet(builder, flattened);
                } else {
                    LLVMBuildRetVoid(builder);
                }
            }
            Either::Left(Stmt::If(cond, then, else_ifs, None)) => {
                let then_block = LLVMAppendBasicBlock(parent, c_str!("then"));
                let merge = LLVMAppendBasicBlock(parent, c_str!("merge"));

                let cond = flatten_expr(context, module, &my_symbols, builder, *cond);
                LLVMBuildCondBr(builder, cond, then_block, merge);

                // Build True Branch
                LLVMPositionBuilderAtEnd(builder, then_block);
                gen_decl(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    then.decl,
                    false,
                );
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    then.commands,
                );
                LLVMBuildBr(builder, merge);

                // Build Merge Branch
                LLVMPositionBuilderAtEnd(builder, merge);
            }
            Either::Left(Stmt::If(cond, then, else_ifs, Some(_else))) => {
                let then_block = LLVMAppendBasicBlock(parent, c_str!("then"));
                let else_block = LLVMAppendBasicBlock(parent, c_str!("else"));
                let merge = LLVMAppendBasicBlock(parent, c_str!("merge"));

                let cond = flatten_expr(context, module, &my_symbols, builder, *cond);
                LLVMBuildCondBr(builder, cond, then_block, else_block);

                // Build True Branch
                LLVMPositionBuilderAtEnd(builder, then_block);
                gen_decl(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    then.decl,
                    false,
                );
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    then.commands,
                );
                LLVMBuildBr(builder, merge);

                // Build False Branch
                LLVMPositionBuilderAtEnd(builder, else_block);
                gen_decl(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    _else.decl,
                    false,
                );
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    _else.commands,
                );
                LLVMBuildBr(builder, merge);

                // Build Merge Branch
                LLVMPositionBuilderAtEnd(builder, merge);
            }
            Either::Left(Stmt::For(init, cond, step, block)) => {
                let cond_block = LLVMAppendBasicBlock(parent, c_str!("cond_loop"));
                let loop_block = LLVMAppendBasicBlock(parent, c_str!("loop"));
                let exit_block = LLVMAppendBasicBlock(parent, c_str!("exit_loop"));

                let init = *init;
                // Build attribution before entering init_block
                if let Stmt::Attr(Variable::Single(v), e) = init {
                    if let Err(s) = build_attr(context, module, &my_symbols, builder, v, *e) {
                        panic!(s);
                    }
                } else if let Stmt::Attr(Variable::Array(v, i), e) = init {
                    println!("uninplemented!");
                } else {
                    panic!("invalid state");
                }
                LLVMBuildBr(builder, cond_block);

                // Build condition inside cond_block
                LLVMPositionBuilderAtEnd(builder, cond_block);
                let cond = flatten_expr(context, module, &my_symbols, builder, *cond);
                LLVMBuildCondBr(builder, cond, loop_block, exit_block);

                // Position at loop to build loop's instructions
                LLVMPositionBuilderAtEnd(builder, loop_block);
                gen_decl(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    block.decl,
                    false,
                );
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    block.commands,
                );

                // Add step to end of loop block
                let step = *step;
                if let Stmt::Attr(Variable::Single(v), e) = step {
                    if let Err(s) = build_attr(context, module, &my_symbols, builder, v, *e) {
                        panic!(s);
                    }
                } else if let Stmt::Attr(Variable::Array(v, i), e) = step {
                    println!("uninplemented!");
                } else {
                    panic!("invalid state");
                }
                LLVMBuildBr(builder, cond_block);

                // Continue at exit_loop
                LLVMPositionBuilderAtEnd(builder, exit_block);
            }

            Either::Left(Stmt::While(cond, block)) => {
                let cond_block = LLVMAppendBasicBlock(parent, c_str!("cond_loop"));
                let loop_block = LLVMAppendBasicBlock(parent, c_str!("loop"));
                let exit_block = LLVMAppendBasicBlock(parent, c_str!("exit_loop"));

                LLVMBuildBr(builder, cond_block);

                LLVMPositionBuilderAtEnd(builder, cond_block);
                // Build condition inside cond_block
                let cond = flatten_expr(context, module, &my_symbols, builder, *cond);
                LLVMBuildCondBr(builder, cond, loop_block, exit_block);

                // Position at loop to build loop's instructions
                LLVMPositionBuilderAtEnd(builder, loop_block);
                gen_decl(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    block.decl,
                    false,
                );
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    block.commands,
                );
                LLVMBuildBr(builder, cond_block);

                // Continue at exit_loop
                LLVMPositionBuilderAtEnd(builder, exit_block);
            }

            Either::Left(_) => println!("uninplemented!"),
            Either::Right(b) => {
                for i in b.decl {
                    match i {
                        Decl::Single(n, t, e) => {
                            local_add_variable(context, module, &mut my_symbols, builder, n, t, e)
                        }
                        Decl::Array(n, t, s, e) => {
                            local_add_array(context, module, &mut my_symbols, builder, n, t, s, e)
                        }
                        _ => panic!("Cannot declare functions inside functions!"),
                    }
                }
                gen_block(
                    context,
                    module,
                    &mut my_symbols,
                    builder,
                    parent,
                    b.commands,
                )
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
