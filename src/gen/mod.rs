use std::ffi::CString;

#[macro_use]
macro_rules! as_str {
    ($s:expr) => {
        CString::new($s.clone()).unwrap().as_ptr()
    };
}

use self::emit::Emit;
use ast::*;
use llvm::core::*;

mod context;
mod emit;
mod symbol_table;

//macro_rules! c_str {
//    ($s:expr) => {{
//        concat!($s, "\0").as_ptr() as *const i8
//    }};
//}
//
//macro_rules! m_str {
//    ($s:expr) => {{
//        concat!($s, "\0").as_ptr() as *mut i8
//    }};
//}
//
//macro_rules! mm_str {
//    ($s:expr) => {{
//        concat!($s, "\0").as_ptr() as *mut *mut i8
//    }};
//}
//
//unsafe fn gen_type(context: LLVMContextRef, t: Option<Type>) -> LLVMTypeRef {
//    match t {
//        Some(Type::Bool) => LLVMInt1TypeInContext(context),
//        Some(Type::Int) => LLVMInt64TypeInContext(context),
//        Some(Type::Str) => panic!("Do not use gen_type with Strings!"),
//        None => LLVMVoidTypeInContext(context),
//    }
//}
//
//unsafe fn gen_array_type(context: LLVMContextRef, t: &Type) -> LLVMTypeRef {
//    match t {
//        Type::Bool => LLVMPointerType(LLVMInt1TypeInContext(context), 0),
//        Type::Int => LLVMPointerType(LLVMInt64TypeInContext(context), 0),
//        Type::Str => panic!("Do not use gen_array_type with Strings!"),
//    }
//}
//
//unsafe fn flatten_expr(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &SymbolTable,
//    builder: LLVMBuilderRef,
//    e: Expr,
//) -> LLVMValueRef {
//    let mut v = Vec::new();
//    match e {
//        Expr::Number(n) => {
//            v.push(LLVMConstInt(gen_type(context, Some(Type::Int)), n, 1));
//        }
//        Expr::Variable(Variable::Single(s)) => {
//            if let Ok(var) = symbols.get(&s) {
//                if let Symbol::Variable(mut var) = var {
//                    let tmp = LLVMBuildLoad(builder, var, c_str!("flat"));
//                    v.push(tmp);
//                } else {
//                    panic!(
//                        "Variable <{:?}> of a type diferent than expected!",
//                        s
//                    );
//                }
//            } else {
//                panic!("Variable <{:?}> is used but not declared!", s);
//            }
//        }
//        Expr::Variable(Variable::Array(s, e)) => {
//            if let Ok(var) = symbols.get(&s) {
//                if let Symbol::ArrayRef(mut var) = var {
//                    let index_flattened =
//                        flatten_expr(context, module, symbols, builder, *e);
//                    let loaded_array_ptr =
//                        LLVMBuildLoad(builder, var, c_str!("loaded_param"));
//                    let arr_at = LLVMBuildInBoundsGEP(
//                        builder,
//                        loaded_array_ptr,
//                        [index_flattened].as_mut_ptr(),
//                        1,
//                        c_str!("arr"),
//                    );
//                    v.push(LLVMBuildLoad(builder, arr_at, c_str!("flat")));
//                } else if let Symbol::Array(_, mut var) = var {
//                    let flattened =
//                        flatten_expr(context, module, symbols, builder, *e);
//                    let arr_at = LLVMBuildGEP(
//                        builder,
//                        var,
//                        [
//                            flattened,
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                0,
//                                1,
//                            ),
//                        ]
//                        .as_mut_ptr(),
//                        2,
//                        c_str!("arr"),
//                    );
//                    v.push(LLVMBuildLoad(builder, arr_at, c_str!("flat")));
//                } else {
//                    panic!("Variable <{:?}> is used but not declared!", s);
//                }
//            } else {
//                panic!("Variable <{:?}> is used but not declared!", s);
//            }
//        }
//        Expr::True => {
//            v.push(LLVMConstInt(gen_type(context, Some(Type::Bool)), 1, 1));
//        }
//        Expr::False => {
//            v.push(LLVMConstInt(gen_type(context, Some(Type::Bool)), 0, 1));
//        }
//        Expr::Op(lhs, op, rhs) => match op {
//            Opcode::Add => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildAdd(builder, lhs, rhs, c_str!("add")));
//            }
//            Opcode::Sub => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildSub(builder, lhs, rhs, c_str!("sub")));
//            }
//            Opcode::Mul => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildMul(builder, lhs, rhs, c_str!("mul")));
//            }
//            Opcode::Div => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildSDiv(builder, lhs, rhs, c_str!("sdiv")));
//            }
//            Opcode::Mod => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildSRem(builder, lhs, rhs, c_str!("srem")));
//            }
//            Opcode::Lesser
//            | Opcode::LesserOrEqual
//            | Opcode::Greater
//            | Opcode::GreaterOrEqual
//            | Opcode::Equal
//            | Opcode::Different => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildICmp(
//                    builder,
//                    op.pred(),
//                    lhs,
//                    rhs,
//                    c_str!("cmp"),
//                ));
//            }
//            Opcode::And => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildAnd(builder, lhs, rhs, c_str!("and")));
//            }
//            Opcode::Or => {
//                let lhs = flatten_expr(context, module, symbols, builder, *lhs);
//                let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//                v.push(LLVMBuildOr(builder, lhs, rhs, c_str!("or")));
//            }
//            _ => panic!("IMPOSSIBURU! Opcode<{:?}> is unary!", op),
//        },
//        Expr::Call(n, None) => {
//            let called_fn = LLVMGetNamedFunction(module, as_str!(n));
//            v.push(LLVMBuildCall(
//                builder,
//                called_fn,
//                [].as_mut_ptr(),
//                0,
//                c_str!("fn_call"),
//            ));
//        }
//        Expr::Right(Opcode::Negative, rhs) => {
//            let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//            v.push(LLVMBuildMul(
//                builder,
//                LLVMConstInt(
//                    gen_type(context, Some(Type::Int)),
//                    -1i64 as u64,
//                    1,
//                ),
//                rhs,
//                c_str!("neg"),
//            ));
//        }
//        Expr::Right(Opcode::Not, rhs) => {
//            let rhs = flatten_expr(context, module, symbols, builder, *rhs);
//            v.push(LLVMBuildNot(builder, rhs, c_str!("not")));
//        }
//        Expr::Right(o, _) => {
//            panic!("IMPOSSIBURU! Opcode<{:?}> is binary!", o);
//        }
//        _ => println!("uninplemented!"),
//    }
//    if let Some(a) = v.last().cloned() {
//        a
//    } else {
//        //panic!("invalid state");
//        LLVMConstInt(gen_type(context, Some(Type::Int)), 42, 1)
//    }
//}
//
//unsafe fn local_add_variable(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    builder: LLVMBuilderRef,
//    n: &str,
//    t: Type,
//    e: Option<Box<Expr>>,
//) {
//    let t = gen_type(context, Some(t));
//    let decl = LLVMBuildAlloca(builder, t, as_str!(n));
//    if let Some(e) = e {
//        let flattened = flatten_expr(context, module, symbols, builder, *e);
//        LLVMBuildStore(builder, flattened, decl);
//    } else {
//        LLVMBuildStore(builder, LLVMConstInt(t, 0, 1), decl);
//    }
//    let new_symbol = Symbol::Variable(decl);
//    symbols.set(&n, new_symbol);
//}
//
//unsafe fn local_add_array(
//    context: LLVMContextRef,
//    symbols: &mut SymbolTable,
//    builder: LLVMBuilderRef,
//    n: &str,
//    t: Type,
//    s: u64,
//    e: Option<Vec<Box<Expr>>>,
//) {
//    let t = gen_type(context, Some(t));
//    let array_type = LLVMArrayType(t, s as u32);
//    let decl = LLVMBuildArrayAlloca(
//        builder,
//        array_type,
//        LLVMConstInt(t, 0, 1),
//        as_str!(n),
//    );
//    if let Some(e) = e {
//        for (i, e) in e.iter().enumerate() {
//            match **e {
//                Expr::Number(e) => {
//                    let ptr = LLVMBuildGEP(
//                        builder,
//                        decl,
//                        [
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                i as u64,
//                                1,
//                            ),
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                0,
//                                1,
//                            ),
//                        ]
//                        .as_mut_ptr(),
//                        2,
//                        c_str!("ptr_get"),
//                    );
//                    LLVMBuildStore(builder, LLVMConstInt(t, e, 1), ptr);
//                }
//                Expr::True => {
//                    let ptr = LLVMBuildGEP(
//                        builder,
//                        decl,
//                        [
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                i as u64,
//                                1,
//                            ),
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                0,
//                                1,
//                            ),
//                        ]
//                        .as_mut_ptr(),
//                        2,
//                        c_str!("ptr_get"),
//                    );
//                    LLVMBuildStore(builder, LLVMConstInt(t, 1, 1), ptr);
//                }
//                Expr::False => {
//                    let ptr = LLVMBuildGEP(
//                        builder,
//                        decl,
//                        [
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                i as u64,
//                                1,
//                            ),
//                            LLVMConstInt(
//                                gen_type(context, Some(Type::Int)),
//                                0,
//                                1,
//                            ),
//                        ]
//                        .as_mut_ptr(),
//                        2,
//                        c_str!("ptr_get"),
//                    );
//                    LLVMBuildStore(builder, LLVMConstInt(t, 0, 1), ptr);
//                }
//                _ => panic!(
//                    "Cannot initialize global value with non-const expresion!"
//                ),
//            };
//        }
//        /*
//         *let mut args = e
//         *    .iter()
//         *    .map(|b| match **b {
//         *        Expr::Number(e) => LLVMConstInt(t, e, 1),
//         *        Expr::True => LLVMConstInt(t, 1, 1),
//         *        Expr::False => LLVMConstInt(t, 0, 1),
//         *        _ => panic!("Cannot initialize global value with non-const expresion!"),
//         *    })
//         *    .collect::<Vec<_>>();
//         *let values = LLVMConstArray(t, args.as_mut_ptr(), args.len() as u32);
//         *LLVMBuildStore(builder, values, decl);
//         */
//    }
//    let new_symbol = Symbol::Array(s as u32, decl);
//
//    symbols.set(&n, new_symbol);
//}
//
//unsafe fn global_add_func(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    n: &str,
//    t: Option<Type>, // Return Type
//    a: Option<Vec<FuncParam>>,
//    b: Block,
//) {
//    let builder = LLVMCreateBuilderInContext(context);
//    let t = gen_type(context, t);
//    let args = if let Some(a) = a {
//        a.iter()
//            .map(|p| match p {
//                FuncParam::Single(n, t) => {
//                    (n.clone(), true, gen_type(context, Some(t.clone())))
//                }
//                FuncParam::Array(n, t) => {
//                    (n.clone(), false, gen_array_type(context, &t.clone()))
//                }
//            })
//            .collect::<Vec<_>>()
//    } else {
//        Vec::new()
//    };
//    let function_type = LLVMFunctionType(
//        t,
//        args.iter().map(|a| a.2).collect::<Vec<_>>().as_mut_ptr(),
//        args.len() as u32,
//        0,
//    );
//    let function = LLVMAddFunction(module, as_str!(n), function_type);
//
//    symbols.initialize_scope();
//
//    let entry =
//        LLVMAppendBasicBlockInContext(context, function, c_str!("entry"));
//    LLVMPositionBuilderAtEnd(builder, entry);
//
//    for (i, e) in args.iter().enumerate() {
//        if e.1 {
//            let fn_param = LLVMGetParam(function, i as u32);
//            let alloced_param = LLVMBuildAlloca(builder, e.2, c_str!("param"));
//            LLVMBuildStore(builder, fn_param, alloced_param);
//            let new_symbol = Symbol::Variable(alloced_param);
//            symbols.set(&e.0, new_symbol);
//        } else {
//            let fn_param = LLVMGetParam(function, i as u32);
//            let alloced_param = LLVMBuildAlloca(builder, e.2, c_str!("param"));
//            LLVMBuildStore(builder, fn_param, alloced_param);
//            let new_symbol = Symbol::ArrayRef(alloced_param);
//            symbols.set(&e.0, new_symbol);
//        }
//    }
//
//    let test = LLVMGetNamedFunction(module, c_str!("printf"));
//    // Stupid way of checking if the function is already defined.
//    let against = ptr::null::<LLVMValueRef>() as *mut _;
//    if test == against {
//        LLVMBuildGlobalStringPtr(builder, c_str!("%d"), c_str!("format_int"));
//        LLVMBuildGlobalStringPtr(builder, c_str!("%s"), c_str!("format_str"));
//
//        let int8_type = LLVMInt8TypeInContext(context);
//        let int32_type = LLVMInt32TypeInContext(context);
//        let mut args = [LLVMPointerType(int8_type, 0)];
//        let fn_type = LLVMFunctionType(int32_type, args.as_mut_ptr(), 0, 1);
//
//        LLVMAddFunction(module, c_str!("printf"), fn_type);
//        LLVMAddFunction(module, c_str!("scanf"), fn_type);
//    }
//
//    gen_decl(context, module, symbols, builder, b.decl, false);
//    gen_block(
//        context, module, symbols, builder, function, None, b.commands,
//    );
//
//    symbols.kill_scope();
//
//    LLVMDisposeBuilder(builder);
//    let new_symbol = Symbol::Func(n.to_string());
//
//    symbols.set(&n, new_symbol);
//}
//
//unsafe fn gen_decl(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    builder: LLVMBuilderRef,
//    decl: Vec<Decl>,
//    allow_fn: bool,
//) {
//    for i in decl {
//        match i {
//            Decl::Single(n, t, e) => {
//                local_add_variable(context, module, symbols, builder, &n, t, e)
//            }
//            Decl::Array(n, t, s, e) => {
//                local_add_array(context, symbols, builder, &n, t, s, e)
//            }
//            Decl::Func(_, _, _, _) => {
//                if allow_fn {
//                    println!("unimplemented");
//                } else {
//                    panic!("Functions are not allowed here!");
//                }
//            }
//        }
//    }
//}
//
//unsafe fn build_attr(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &SymbolTable,
//    builder: LLVMBuilderRef,
//    v: &str,
//    e: Expr,
//) -> Result<(), String> {
//    if let Ok(var) = symbols.get(&v) {
//        if let Symbol::Variable(mut var) = var {
//            let flattened = flatten_expr(context, module, symbols, builder, e);
//            LLVMBuildStore(builder, flattened, var);
//            Ok(())
//        } else {
//            Err(format!("Variable <{:?}> is used but not declared!", v))
//        }
//    } else {
//        Err(format!("Variable <{:?}> is used but not declared!", v))
//    }
//}
//
//unsafe fn gen_block(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    builder: LLVMBuilderRef,
//    parent: LLVMValueRef,
//    looping: Option<(LLVMBasicBlockRef, LLVMBasicBlockRef)>,
//    stmts: Vec<Either<Stmt, Block>>,
//) {
//    symbols.initialize_scope();
//
//    for i in stmts {
//        match i {
//            Either::Left(Stmt::Attr(Variable::Single(v), e)) => {
//                if let Err(s) =
//                    build_attr(context, module, symbols, builder, &v, *e)
//                {
//                    panic!(s);
//                }
//            }
//            Either::Left(Stmt::Write(vec)) => {
//                for i in vec {
//                    let flattened =
//                        flatten_expr(context, module, symbols, builder, *i);
//                    let format_str =
//                        LLVMGetNamedGlobal(module, c_str!("format_int"));
//                    let mut printf_args = [format_str, flattened];
//                    let printf_fn =
//                        LLVMGetNamedFunction(module, c_str!("printf"));
//                    LLVMBuildCall(
//                        builder,
//                        printf_fn,
//                        printf_args.as_mut_ptr(),
//                        2,
//                        c_str!("write"),
//                    );
//                }
//            }
//            Either::Left(Stmt::Read(Variable::Single(v))) => {
//                if let Ok(var) = symbols.get(&v) {
//                    if let Symbol::Variable(mut var) = var {
//                        let format_str =
//                            LLVMGetNamedGlobal(module, c_str!("format_int"));
//                        let mut scanf_args = [format_str, var];
//                        let scanf_fn =
//                            LLVMGetNamedFunction(module, c_str!("scanf"));
//                        LLVMBuildCall(
//                            builder,
//                            scanf_fn,
//                            scanf_args.as_mut_ptr(),
//                            2,
//                            c_str!("read"),
//                        );
//                    }
//                }
//            }
//            Either::Left(Stmt::Read(Variable::Array(v, e))) => {
//                if let Ok(var) = symbols.get(&v) {
//                    if let Symbol::ArrayRef(mut var) = var {
//                        let flattened =
//                            flatten_expr(context, module, symbols, builder, *e);
//                        let arr_at = LLVMBuildGEP(
//                            builder,
//                            var,
//                            [
//                                LLVMConstInt(
//                                    gen_type(context, Some(Type::Int)),
//                                    0,
//                                    1,
//                                ),
//                                flattened,
//                            ]
//                            .as_mut_ptr(),
//                            2,
//                            c_str!("arr"),
//                        );
//                        let format_str =
//                            LLVMGetNamedGlobal(module, c_str!("format_int"));
//                        let mut scanf_args = [format_str, arr_at];
//                        let scanf_fn =
//                            LLVMGetNamedFunction(module, c_str!("scanf"));
//                        LLVMBuildCall(
//                            builder,
//                            scanf_fn,
//                            scanf_args.as_mut_ptr(),
//                            2,
//                            c_str!("read"),
//                        );
//                    } else if let Symbol::Array(_, mut var) = var {
//                        let flattened =
//                            flatten_expr(context, module, symbols, builder, *e);
//                        let arr_at = LLVMBuildGEP(
//                            builder,
//                            var,
//                            [
//                                LLVMConstInt(
//                                    gen_type(context, Some(Type::Int)),
//                                    0,
//                                    1,
//                                ),
//                                flattened,
//                            ]
//                            .as_mut_ptr(),
//                            2,
//                            c_str!("arr"),
//                        );
//                        let format_str =
//                            LLVMGetNamedGlobal(module, c_str!("format_int"));
//                        let mut scanf_args = [format_str, arr_at];
//                        let scanf_fn =
//                            LLVMGetNamedFunction(module, c_str!("scanf"));
//                        LLVMBuildCall(
//                            builder,
//                            scanf_fn,
//                            scanf_args.as_mut_ptr(),
//                            2,
//                            c_str!("read"),
//                        );
//                    }
//                }
//            }
//            Either::Left(Stmt::Call(n, None)) => {
//                let called_fn = LLVMGetNamedFunction(module, as_str!(n));
//                LLVMBuildCall(
//                    builder,
//                    called_fn,
//                    [].as_mut_ptr(),
//                    0,
//                    c_str!(""),
//                );
//            }
//            Either::Left(Stmt::Skip) => {
//                if let Some((skip, _)) = looping {
//                    LLVMBuildBr(builder, skip);
//                } else {
//                    panic!("cannot use skip outside of a loop");
//                }
//            }
//            Either::Left(Stmt::Stop) => {
//                if let Some((_, stop)) = looping {
//                    LLVMBuildBr(builder, stop);
//                } else {
//                    panic!("cannot use skip outside of a loop");
//                }
//            }
//            Either::Left(Stmt::Return(v)) => {
//                if let Some(v) = v {
//                    let flattened =
//                        flatten_expr(context, module, symbols, builder, *v);
//                    LLVMBuildRet(builder, flattened);
//                } else {
//                    LLVMBuildRetVoid(builder);
//                }
//            }
//            Either::Left(Stmt::If(cond, then, else_ifs, None)) => {
//                let then_block = LLVMAppendBasicBlock(parent, c_str!("then"));
//                let merge = LLVMAppendBasicBlock(parent, c_str!("merge"));
//
//                let cond =
//                    flatten_expr(context, module, symbols, builder, *cond);
//                LLVMBuildCondBr(builder, cond, then_block, merge);
//
//                // Build True Branch
//                LLVMPositionBuilderAtEnd(builder, then_block);
//                gen_decl(context, module, symbols, builder, then.decl, false);
//                gen_block(
//                    context,
//                    module,
//                    symbols,
//                    builder,
//                    parent,
//                    looping,
//                    then.commands,
//                );
//                LLVMBuildBr(builder, merge);
//
//                // Build Merge Branch
//                LLVMPositionBuilderAtEnd(builder, merge);
//            }
//            Either::Left(Stmt::If(cond, then, else_ifs, Some(_else))) => {
//                let then_block = LLVMAppendBasicBlock(parent, c_str!("then"));
//                let else_block = LLVMAppendBasicBlock(parent, c_str!("else"));
//                let merge = LLVMAppendBasicBlock(parent, c_str!("merge"));
//
//                let cond =
//                    flatten_expr(context, module, symbols, builder, *cond);
//                LLVMBuildCondBr(builder, cond, then_block, else_block);
//
//                // Build True Branch
//                LLVMPositionBuilderAtEnd(builder, then_block);
//                gen_decl(context, module, symbols, builder, then.decl, false);
//                gen_block(
//                    context,
//                    module,
//                    symbols,
//                    builder,
//                    parent,
//                    looping,
//                    then.commands,
//                );
//                LLVMBuildBr(builder, merge);
//
//                // Build False Branch
//                LLVMPositionBuilderAtEnd(builder, else_block);
//                gen_decl(context, module, symbols, builder, _else.decl, false);
//                gen_block(
//                    context,
//                    module,
//                    symbols,
//                    builder,
//                    parent,
//                    looping,
//                    _else.commands,
//                );
//                LLVMBuildBr(builder, merge);
//
//                // Build Merge Branch
//                LLVMPositionBuilderAtEnd(builder, merge);
//            }
//            Either::Left(Stmt::For(init, cond, step, block)) => {
//                let cond_block =
//                    LLVMAppendBasicBlock(parent, c_str!("cond_loop"));
//                let loop_block = LLVMAppendBasicBlock(parent, c_str!("loop"));
//                let step_block = LLVMAppendBasicBlock(parent, c_str!("step"));
//                let exit_block =
//                    LLVMAppendBasicBlock(parent, c_str!("exit_loop"));
//
//                let init = *init;
//                // Build attribution before entering init_block
//                if let Stmt::Attr(Variable::Single(v), e) = init {
//                    if let Err(s) =
//                        build_attr(context, module, symbols, builder, &v, *e)
//                    {
//                        panic!(s);
//                    }
//                } else if let Stmt::Attr(Variable::Array(v, i), e) = init {
//                    println!("uninplemented!");
//                } else {
//                    panic!("invalid state");
//                }
//                LLVMBuildBr(builder, cond_block);
//
//                // Build condition inside cond_block
//                LLVMPositionBuilderAtEnd(builder, cond_block);
//                let cond =
//                    flatten_expr(context, module, symbols, builder, *cond);
//                LLVMBuildCondBr(builder, cond, loop_block, exit_block);
//
//                // Position at loop to build loop's instructions
//                LLVMPositionBuilderAtEnd(builder, loop_block);
//                gen_decl(context, module, symbols, builder, block.decl, false);
//                gen_block(
//                    context,
//                    module,
//                    symbols,
//                    builder,
//                    parent,
//                    Some((step_block, exit_block)),
//                    block.commands,
//                );
//                LLVMBuildBr(builder, step_block);
//
//                LLVMPositionBuilderAtEnd(builder, step_block);
//                // Add step to end of loop block
//                let step = *step;
//                if let Stmt::Attr(Variable::Single(v), e) = step {
//                    if let Err(s) =
//                        build_attr(context, module, symbols, builder, &v, *e)
//                    {
//                        panic!(s);
//                    }
//                } else if let Stmt::Attr(Variable::Array(v, i), e) = step {
//                    println!("uninplemented!");
//                } else {
//                    panic!("invalid state");
//                }
//                LLVMBuildBr(builder, cond_block);
//
//                // Continue at exit_loop
//                LLVMPositionBuilderAtEnd(builder, exit_block);
//            }
//
//            Either::Left(Stmt::While(cond, block)) => {
//                let cond_block =
//                    LLVMAppendBasicBlock(parent, c_str!("cond_loop"));
//                let loop_block = LLVMAppendBasicBlock(parent, c_str!("loop"));
//                let exit_block =
//                    LLVMAppendBasicBlock(parent, c_str!("exit_loop"));
//
//                LLVMBuildBr(builder, cond_block);
//
//                LLVMPositionBuilderAtEnd(builder, cond_block);
//                // Build condition inside cond_block
//                let cond =
//                    flatten_expr(context, module, symbols, builder, *cond);
//                LLVMBuildCondBr(builder, cond, loop_block, exit_block);
//
//                // Position at loop to build loop's instructions
//                LLVMPositionBuilderAtEnd(builder, loop_block);
//                gen_decl(context, module, symbols, builder, block.decl, false);
//                gen_block(
//                    context,
//                    module,
//                    symbols,
//                    builder,
//                    parent,
//                    Some((cond_block, exit_block)),
//                    block.commands,
//                );
//                LLVMBuildBr(builder, cond_block);
//
//                // Continue at exit_loop
//                LLVMPositionBuilderAtEnd(builder, exit_block);
//            }
//
//            Either::Left(_) => println!("uninplemented!"),
//            Either::Right(b) => {
//                for i in b.decl {
//                    match i {
//                        Decl::Single(n, t, e) => local_add_variable(
//                            context, module, symbols, builder, &n, t, e,
//                        ),
//                        Decl::Array(n, t, s, e) => local_add_array(
//                            context, symbols, builder, &n, t, s, e,
//                        ),
//                        _ => {
//                            panic!("Cannot declare functions inside functions!")
//                        }
//                    }
//                }
//                gen_block(
//                    context, module, symbols, builder, parent, looping,
//                    b.commands,
//                )
//            }
//        }
//    }
//
//    symbols.kill_scope();
//}
//
//unsafe fn global_add_variable(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    n: &str,
//    t: Type,
//    e: Option<Box<Expr>>,
//) {
//    let t = gen_type(context, Some(t));
//    let decl = LLVMAddGlobal(module, t, as_str!(n));
//    if let Some(e) = e {
//        let b = *e;
//        if let Expr::Number(v) = b {
//            LLVMSetInitializer(decl, LLVMConstInt(t, v as u64, 1));
//        }
//    } else {
//        panic!("Cannot initialize global value with non-const expresion!");
//    }
//    let new_symbol = Symbol::Variable(decl);
//    symbols.set(&n, new_symbol);
//}
//
//unsafe fn global_add_array(
//    context: LLVMContextRef,
//    module: LLVMModuleRef,
//    symbols: &mut SymbolTable,
//    n: &str,
//    t: Type,
//    s: u64,
//    e: Option<Vec<Box<Expr>>>,
//) {
//    let t = gen_type(context, Some(t));
//    let array_type = LLVMArrayType(t, s as u32);
//    let decl = LLVMAddGlobal(module, array_type, as_str!(n));
//    if let Some(e) = e {
//        let mut args = e
//            .iter()
//            .map(|b| match **b {
//                Expr::Number(e) => LLVMConstInt(t, e, 1),
//                Expr::True => LLVMConstInt(t, 1, 1),
//                Expr::False => LLVMConstInt(t, 0, 1),
//                _ => panic!(
//                    "Cannot initialize global value with non-const expresion!"
//                ),
//            })
//            .collect::<Vec<_>>();
//        let values = LLVMConstArray(t, args.as_mut_ptr(), args.len() as u32);
//        LLVMSetInitializer(decl, values);
//    }
//    let new_symbol = Symbol::Array(s as u32, decl);
//    symbols.set(&n, new_symbol);
//}

pub unsafe fn gen(decls: Vec<Decl>) {
    let mut context = context::Context::new();
    for i in decls {
        i.emit(&mut context).expect("Cannot emit this");
    }
    LLVMDumpModule(context.module);
    LLVMPrintModuleToFile(
        context.module,
        as_str!("test.ll"),
        as_str!("idk") as *mut *mut i8,
    );
    LLVMContextDispose(context.context);
}
