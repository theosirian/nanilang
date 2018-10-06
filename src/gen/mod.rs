mod array;

use self::array::*;
use ast::*;
use llvm::core::*;
use llvm::prelude::*;

use std::collections::HashMap;
use std::ffi::*;
use std::iter;
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
        CString::new($v.clone(),).unwrap().as_ptr() as *const i8
    };
}

struct Module {
    context: LLVMContextRef,
    module: LLVMModuleRef,
    symbols: HashMap<String, Vec<Symbol,>,>,
    builder: LLVMBuilderRef,
}

struct Function<'function,> {
    module: &'function Module,
    symbols: HashMap<String, Vec<Symbol,>,>,
    value: LLVMValueRef,
}

struct Scope<'scope,> {
    function: &'scope Function<'scope,>,
    symbols: HashMap<String, Vec<Symbol,>,>,
}

impl<'scope,> Scope<'scope,> {
    unsafe fn new(
        function: &'scope Function<'scope,>,
        name: *const i8,
        b: Block,
    ) -> Scope<'scope,> {
        let entry = LLVMAppendBasicBlockInContext(
            function.module.context,
            function.value,
            name,
        );

        let symbols = function.symbols.clone();

        LLVMPositionBuilderAtEnd(function.module.builder, entry,);

        let mut scope = Scope { function, symbols, };

        scope.gen_decl(&function.value, b.decl, false,);
        scope.gen_block(&function.value, None, b.commands,);

        LLVMDisposeBuilder(function.module.builder,);

        scope
    }

    unsafe fn get_variable(
        self: &Scope<'scope,>,
        var: Variable,
    ) -> LLVMValueRef {
        match var {
            Variable::Single(s,) => {
                if let Some(vec,) = self.symbols.get(&s,) {
                    if let Some(Symbol::Variable(mut var,),) =
                        vec.last().clone()
                    {
                        LLVMBuildLoad(
                            self.function.module.builder,
                            var,
                            c_str!("flat"),
                        )
                    } else {
                        panic!("Variable <{:?}> is used but not declared!", s);
                    }
                } else {
                    panic!("Variable <{:?}> is used but not declared!", s);
                }
            }
            Variable::Array(s, e,) => {
                if let Some(vec,) = self.symbols.get(&s,) {
                    match vec.last().clone() {
                        Some(Symbol::ArrayRef(mut array,),)
                        | Some(Symbol::Array(_, mut array,),) => {
                            let ptr = LLVMBuildGEP(
                                self.function.module.builder,
                                array,
                                [
                                    self.flatten_expr(*e,),
                                    LLVMConstInt(
                                        self.function
                                            .module
                                            .gen_type(Some(Type::Int,),),
                                        0,
                                        1,
                                    ),
                                ].as_mut_ptr(),
                                2,
                                c_str!("ptr_get"),
                            );
                            LLVMBuildLoad(
                                self.function.module.builder,
                                ptr,
                                c_str!("arr_at"),
                            )
                        }
                        _ => {
                            panic!(
                                "Variable <{:?}> is used but not declared!",
                                s
                            );
                        }
                    }
                } else {
                    panic!("Variable <{:?}> is used but not declared!", s);
                }
            }
        }
    }

    unsafe fn flatten_expr(self: &Scope<'scope,>, e: Expr,) -> LLVMValueRef {
        let mut v = Vec::new();
        match e {
            Expr::Number(n,) => {
                v.push(LLVMConstInt(
                    self.function.module.gen_type(Some(Type::Int,),),
                    n,
                    1,
                ),);
            }
            Expr::Variable(var,) => {
                v.push(self.get_variable(var,),);
            }
            Expr::True => {
                v.push(LLVMConstInt(
                    self.function.module.gen_type(Some(Type::Bool,),),
                    1,
                    1,
                ),);
            }
            Expr::False => {
                v.push(LLVMConstInt(
                    self.function.module.gen_type(Some(Type::Bool,),),
                    0,
                    1,
                ),);
            }
            Expr::Op(lhs, op, rhs,) => match op {
                Opcode::Add => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildAdd(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("add"),
                    ),);
                }
                Opcode::Sub => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildSub(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("sub"),
                    ),);
                }
                Opcode::Mul => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildMul(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("mul"),
                    ),);
                }
                Opcode::Div => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildSDiv(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("sdiv"),
                    ),);
                }
                Opcode::Mod => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildSRem(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("srem"),
                    ),);
                }
                Opcode::Lesser
                | Opcode::LesserOrEqual
                | Opcode::Greater
                | Opcode::GreaterOrEqual
                | Opcode::Equal
                | Opcode::Different => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildICmp(
                        self.function.module.builder,
                        op.pred(),
                        lhs,
                        rhs,
                        c_str!("cmp"),
                    ),);
                }
                Opcode::And => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildAnd(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("and"),
                    ),);
                }
                Opcode::Or => {
                    let lhs = self.flatten_expr(*lhs,);
                    let rhs = self.flatten_expr(*rhs,);
                    v.push(LLVMBuildOr(
                        self.function.module.builder,
                        lhs,
                        rhs,
                        c_str!("or"),
                    ),);
                }
                _ => panic!("IMPOSSIBURU! Opcode<{:?}> is unary!", op),
            },
            Expr::Call(n, None,) => {
                let called_fn = LLVMGetNamedFunction(
                    self.function.module.module,
                    as_str!(n),
                );
                v.push(LLVMBuildCall(
                    self.function.module.builder,
                    called_fn,
                    [].as_mut_ptr(),
                    0,
                    c_str!("fn_call"),
                ),);
            }
            Expr::Right(Opcode::Negative, rhs,) => {
                let rhs = self.flatten_expr(*rhs,);
                v.push(LLVMBuildMul(
                    self.function.module.builder,
                    LLVMConstInt(
                        self.function.module.gen_type(Some(Type::Int,),),
                        -1i64 as u64,
                        1,
                    ),
                    rhs,
                    c_str!("neg"),
                ),);
            }
            Expr::Right(Opcode::Not, rhs,) => {
                let rhs = self.flatten_expr(*rhs,);
                v.push(LLVMBuildNot(
                    self.function.module.builder,
                    rhs,
                    c_str!("not"),
                ),);
            }
            Expr::Right(o, _,) => {
                panic!("IMPOSSIBURU! Opcode<{:?}> is binary!", o);
            }
            _ => println!("uninplemented!"),
        }
        if let Some(a,) = v.last().cloned() {
            a
        } else {
            //panic!("invalid state");
            LLVMConstInt(
                self.function.module.gen_type(Some(Type::Int,),),
                42,
                1,
            )
        }
    }

    unsafe fn local_add_variable(
        self: &mut Scope<'scope,>,
        n: String,
        t: Type,
        e: Option<Box<Expr,>,>,
    ) {
        let t = self.function.module.gen_type(Some(t,),);
        let decl =
            LLVMBuildAlloca(self.function.module.builder, t, as_str!(n),);
        if let Some(e,) = e {
            let flattened = self.flatten_expr(*e,);
            LLVMBuildStore(self.function.module.builder, flattened, decl,);
        } else {
            LLVMBuildStore(
                self.function.module.builder,
                LLVMConstInt(t, 0, 1,),
                decl,
            );
        }
        let new_symbol = Symbol::Variable(decl,);
        self.symbols
            .entry(n,)
            .or_insert(Vec::new(),)
            .push(new_symbol,);
    }

    unsafe fn local_add_array(
        self: &mut Scope<'scope,>,
        n: String,
        t: Type,
        s: u64,
        e: Option<Vec<Box<Expr,>,>,>,
    ) {
        let t = &self.function.module.gen_type(Some(t,),);
        let array_type = LLVMArrayType(*t, s as u32,);
        let decl = LLVMBuildArrayAlloca(
            self.function.module.builder,
            array_type,
            LLVMConstInt(*t, 0, 1,),
            as_str!(n),
        );
        if let Some(e) = e {
        for (i, e) in e.iter().enumerate() {
            match **e {
                Expr::Number(e) => {
                    let ptr = LLVMBuildGEP(
                        self.function.module.builder,
                        decl,
                        [
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                i as u64,
                                1,
                            ),
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                0,
                                1,
                            ),
                        ].as_mut_ptr(),
                        2,
                        c_str!("ptr_get"),
                    );
                    LLVMBuildStore(self.function.module.builder, LLVMConstInt(*t, e, 1), ptr);
                }
                Expr::True => {
                    let ptr = LLVMBuildGEP(
                        self.function.module.builder,
                        decl,
                        [
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                i as u64,
                                1,
                            ),
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                0,
                                1,
                            ),
                        ].as_mut_ptr(),
                        2,
                        c_str!("ptr_get"),
                    );
                    LLVMBuildStore(self.function.module.builder, LLVMConstInt(*t, 1, 1), ptr);
                }
                Expr::False => {
                    let ptr = LLVMBuildGEP(
                        self.function.module.builder,
                        decl,
                        [
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                i as u64,
                                1,
                            ),
                            LLVMConstInt(
                                self.function.module.gen_type(Some(Type::Int)),
                                0,
                                1,
                            ),
                        ].as_mut_ptr(),
                        2,
                        c_str!("ptr_get"),
                    );
                    LLVMBuildStore(self.function.module.builder, LLVMConstInt(*t, 0, 1), ptr);
                }
                _ => panic!(
                    "Cannot initialize global value with non-const expresion!"
                ),
            };
        }
        /*
         *let mut args = e
         *    .iter()
         *    .map(|b| match **b {
         *        Expr::Number(e) => LLVMConstInt(t, e, 1),
         *        Expr::True => LLVMConstInt(t, 1, 1),
         *        Expr::False => LLVMConstInt(t, 0, 1),
         *        _ => panic!("Cannot initialize global value with non-const expresion!"),
         *    })
         *    .collect::<Vec<_>>();
         *let values = LLVMConstArray(t, args.as_mut_ptr(), args.len() as u32);
         *LLVMBuildStore(builder, values, decl);
         */
    }
        let new_symbol = Symbol::Array(s as u32, decl,);
        self.symbols
            .entry(n,)
            .or_insert(Vec::new(),)
            .push(new_symbol,);
    }

    unsafe fn gen_decl(
        self: &mut Scope<'scope,>,
        parent: &LLVMValueRef,
        decl: Vec<Decl,>,
        allow_fn: bool,
    ) {
        for i in decl {
            match i {
                Decl::Single(n, t, e,) => self.local_add_variable(n, t, e,),
                Decl::Array(n, t, s, e,) => self.local_add_array(n, t, s, e,),
                Decl::Func(_, _, _, _,) => {
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
        self: &mut Scope<'scope,>,
        v: String,
        e: Expr,
    ) -> Result<(), String,> {
        if let Some(vec,) = self.symbols.get(&v,) {
            if let Some(Symbol::Variable(mut var,),) = vec.last() {
                let flattened = self.flatten_expr(e,);
                LLVMBuildStore(self.function.module.builder, flattened, var,);
                Ok((),)
            } else {
                Err(format!("Variable <{:?}> is used but not declared!", v),)
            }
        } else {
            Err(format!("Variable <{:?}> is used but not declared!", v),)
        }
    }

    unsafe fn gen_block(
        self: &mut Scope<'scope,>,
        parent: &LLVMValueRef,
        looping: Option<(LLVMBasicBlockRef, LLVMBasicBlockRef,),>,
        stmts: Vec<Either<Stmt, Block,>,>,
    ) {
        // This deep clones the Vector as far as tested.
        let my_symbols = self.symbols.clone();
        for i in stmts {
            match i {
                Either::Left(Stmt::Attr(Variable::Single(v,), e,),) => {
                    if let Err(s,) = self.build_attr(v, *e,) {
                        panic!(s);
                    }
                }
                Either::Left(Stmt::Write(vec,),) => {
                    for i in vec {
                        let flattened = self.flatten_expr(*i,);
                        let format_str = LLVMGetNamedGlobal(
                            self.function.module.module,
                            c_str!("format_int"),
                        );
                        let mut printf_args = [format_str, flattened,];
                        let printf_fn = LLVMGetNamedFunction(
                            self.function.module.module,
                            c_str!("printf"),
                        );
                        LLVMBuildCall(
                            self.function.module.builder,
                            printf_fn,
                            printf_args.as_mut_ptr(),
                            2,
                            c_str!("write"),
                        );
                    }
                }
                Either::Left(Stmt::Read(Variable::Single(v,),),) => {
                    if let Some(vec,) = my_symbols.get(&v,) {
                        if let Some(Symbol::Variable(mut var,),) = vec.last() {
                            let format_str = LLVMGetNamedGlobal(
                                self.function.module.module,
                                c_str!("format_int"),
                            );
                            let mut scanf_args = [format_str, var,];
                            let scanf_fn = LLVMGetNamedFunction(
                                self.function.module.module,
                                c_str!("scanf"),
                            );
                            LLVMBuildCall(
                                self.function.module.builder,
                                scanf_fn,
                                scanf_args.as_mut_ptr(),
                                2,
                                c_str!("read"),
                            );
                        }
                    }
                }
                Either::Left(Stmt::Read(Variable::Array(v, e,),),) => {
                    if let Some(vec,) = my_symbols.get(&v,) {
                        if let Some(Symbol::ArrayRef(mut var,),) = vec.last() {
                            let flattened = self.flatten_expr(*e,);
                            let arr_at = LLVMBuildGEP(
                                self.function.module.builder,
                                var,
                                [
                                    LLVMConstInt(
                                        self.function
                                            .module
                                            .gen_type(Some(Type::Int,),),
                                        0,
                                        1,
                                    ),
                                    flattened,
                                ].as_mut_ptr(),
                                2,
                                c_str!("arr"),
                            );
                            let format_str = LLVMGetNamedGlobal(
                                self.function.module.module,
                                c_str!("format_int"),
                            );
                            let mut scanf_args = [format_str, arr_at,];
                            let scanf_fn = LLVMGetNamedFunction(
                                self.function.module.module,
                                c_str!("scanf"),
                            );
                            LLVMBuildCall(
                                self.function.module.builder,
                                scanf_fn,
                                scanf_args.as_mut_ptr(),
                                2,
                                c_str!("read"),
                            );
                        } else if let Some(Symbol::Array(_, mut var,),) =
                            vec.last()
                        {
                            let flattened = self.flatten_expr(*e,);
                            let arr_at = LLVMBuildGEP(
                                self.function.module.builder,
                                var,
                                [
                                    LLVMConstInt(
                                        self.function
                                            .module
                                            .gen_type(Some(Type::Int,),),
                                        0,
                                        1,
                                    ),
                                    flattened,
                                ].as_mut_ptr(),
                                2,
                                c_str!("arr"),
                            );
                            let format_str = LLVMGetNamedGlobal(
                                self.function.module.module,
                                c_str!("format_int"),
                            );
                            let mut scanf_args = [format_str, arr_at,];
                            let scanf_fn = LLVMGetNamedFunction(
                                self.function.module.module,
                                c_str!("scanf"),
                            );
                            LLVMBuildCall(
                                self.function.module.builder,
                                scanf_fn,
                                scanf_args.as_mut_ptr(),
                                2,
                                c_str!("read"),
                            );
                        }
                    }
                }
                Either::Left(Stmt::Call(n, None,),) => {
                    let called_fn = LLVMGetNamedFunction(
                        self.function.module.module,
                        as_str!(n),
                    );
                    LLVMBuildCall(
                        self.function.module.builder,
                        called_fn,
                        [].as_mut_ptr(),
                        0,
                        c_str!(""),
                    );
                }
                Either::Left(Stmt::Skip,) => {
                    if let Some((skip, _,),) = looping {
                        LLVMBuildBr(self.function.module.builder, skip,);
                    } else {
                        panic!("cannot use skip outside of a loop");
                    }
                }
                Either::Left(Stmt::Stop,) => {
                    if let Some((_, stop,),) = looping {
                        LLVMBuildBr(self.function.module.builder, stop,);
                    } else {
                        panic!("cannot use skip outside of a loop");
                    }
                }
                Either::Left(Stmt::Return(v,),) => {
                    if let Some(v,) = v {
                        let flattened = self.flatten_expr(*v,);
                        LLVMBuildRet(self.function.module.builder, flattened,);
                    } else {
                        LLVMBuildRetVoid(self.function.module.builder,);
                    }
                }
                Either::Left(Stmt::If(cond, then, else_ifs, None,),) => {
                    let then_block =
                        LLVMAppendBasicBlock(*parent, c_str!("then"),);
                    let merge = LLVMAppendBasicBlock(*parent, c_str!("merge"),);

                    let cond = self.flatten_expr(*cond,);
                    LLVMBuildCondBr(
                        self.function.module.builder,
                        cond,
                        then_block,
                        merge,
                    );

                    // Build True Branch
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        then_block,
                    );
                    self.gen_decl(parent, then.decl, false,);
                    self.gen_block(parent, looping, then.commands,);
                    LLVMBuildBr(self.function.module.builder, merge,);

                    // Build Merge Branch
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        merge,
                    );
                }
                Either::Left(Stmt::If(cond, then, else_ifs, Some(_else,),),) => {
                    let then_block =
                        LLVMAppendBasicBlock(*parent, c_str!("then"),);
                    let else_block =
                        LLVMAppendBasicBlock(*parent, c_str!("else"),);
                    let merge = LLVMAppendBasicBlock(*parent, c_str!("merge"),);

                    let cond = self.flatten_expr(*cond,);
                    LLVMBuildCondBr(
                        self.function.module.builder,
                        cond,
                        then_block,
                        else_block,
                    );

                    // Build True Branch
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        then_block,
                    );
                    self.gen_decl(parent, then.decl, false,);
                    self.gen_block(parent, looping, then.commands,);
                    LLVMBuildBr(self.function.module.builder, merge,);

                    // Build False Branch
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        else_block,
                    );
                    self.gen_decl(parent, _else.decl, false,);
                    self.gen_block(parent, looping, _else.commands,);
                    LLVMBuildBr(self.function.module.builder, merge,);

                    // Build Merge Branch
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        merge,
                    );
                }
                Either::Left(Stmt::For(init, cond, step, block,),) => {
                    let cond_block =
                        LLVMAppendBasicBlock(*parent, c_str!("cond_loop"),);
                    let loop_block =
                        LLVMAppendBasicBlock(*parent, c_str!("loop"),);
                    let step_block =
                        LLVMAppendBasicBlock(*parent, c_str!("step"),);
                    let exit_block =
                        LLVMAppendBasicBlock(*parent, c_str!("exit_loop"),);

                    let init = *init;
                    // Build attribution before entering init_block
                    if let Stmt::Attr(Variable::Single(v,), e,) = init {
                        if let Err(s,) = self.build_attr(v, *e,) {
                            panic!(s);
                        }
                    } else if let Stmt::Attr(Variable::Array(v, i,), e,) = init
                    {
                        if let Some(vec,) = my_symbols.get(&v,) {
                            if let Some(Symbol::ArrayRef(mut var,),) =
                                vec.last()
                            {
                                let expr_flattened = self.flatten_expr(*e,);
                                let index_flattened = self.flatten_expr(*i,);
                                LLVMBuildInsertElement(
                                    self.function.module.builder,
                                    var,
                                    expr_flattened,
                                    index_flattened,
                                    c_str!("insert_on_vec"),
                                );
                            }
                        }
                    } else {
                        panic!("invalid state");
                    }
                    LLVMBuildBr(self.function.module.builder, cond_block,);

                    // Build condition inside cond_block
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        cond_block,
                    );
                    let cond = self.flatten_expr(*cond,);
                    LLVMBuildCondBr(
                        self.function.module.builder,
                        cond,
                        loop_block,
                        exit_block,
                    );

                    // Position at loop to build loop's instructions
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        loop_block,
                    );
                    self.gen_decl(parent, block.decl, false,);
                    self.gen_block(
                        parent,
                        Some((step_block, exit_block,),),
                        block.commands,
                    );
                    LLVMBuildBr(self.function.module.builder, step_block,);

                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        step_block,
                    );
                    // Add step to end of loop block
                    let step = *step;
                    if let Stmt::Attr(Variable::Single(v,), e,) = step {
                        if let Err(s,) = self.build_attr(v, *e,) {
                            panic!(s);
                        }
                    } else if let Stmt::Attr(Variable::Array(v, i,), e,) = step
                    {
                        if let Some(vec,) = self.symbols.get(&v,) {
                            if let Some(Symbol::ArrayRef(mut var,),) =
                                vec.last()
                            {
                                let expr_flattened = self.flatten_expr(*e,);
                                let index_flattened = self.flatten_expr(*i,);
                                LLVMBuildInsertElement(
                                    self.function.module.builder,
                                    var,
                                    expr_flattened,
                                    index_flattened,
                                    c_str!("insert_on_vec"),
                                );
                            }
                        }
                    } else {
                        panic!("invalid state");
                    }
                    LLVMBuildBr(self.function.module.builder, cond_block,);

                    // Continue at exit_loop
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        exit_block,
                    );
                }

                Either::Left(Stmt::While(cond, block,),) => {
                    let cond_block =
                        LLVMAppendBasicBlock(*parent, c_str!("cond_loop"),);
                    let loop_block =
                        LLVMAppendBasicBlock(*parent, c_str!("loop"),);
                    let exit_block =
                        LLVMAppendBasicBlock(*parent, c_str!("exit_loop"),);

                    LLVMBuildBr(self.function.module.builder, cond_block,);

                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        cond_block,
                    );
                    // Build condition inside cond_block
                    let cond = self.flatten_expr(*cond,);
                    LLVMBuildCondBr(
                        self.function.module.builder,
                        cond,
                        loop_block,
                        exit_block,
                    );

                    // Position at loop to build loop's instructions
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        loop_block,
                    );
                    self.gen_decl(parent, block.decl, false,);
                    self.gen_block(
                        parent,
                        Some((cond_block, exit_block,),),
                        block.commands,
                    );
                    LLVMBuildBr(self.function.module.builder, cond_block,);

                    // Continue at exit_loop
                    LLVMPositionBuilderAtEnd(
                        self.function.module.builder,
                        exit_block,
                    );
                }

                Either::Left(_,) => println!("uninplemented!"),
                Either::Right(b,) => {
                    for i in b.decl {
                        match i {
                            Decl::Single(n, t, e,) => {
                                self.local_add_variable(n, t, e,)
                            }
                            Decl::Array(n, t, s, e,) => {
                                self.local_add_array(n, t, s, e,)
                            }
                            _ => panic!(
                                "Cannot declare functions inside functions!"
                            ),
                        }
                    }
                    self.gen_block(parent, looping, b.commands,)
                }
            }
        }
    }
}

impl<'function,> Function<'function,> {
    unsafe fn new(
        module: &'function Module,
        name: String,
        t: Type,
        a: Option<Vec<FuncParam,>,>,
    ) -> Function<'function,> {
        let mut symbols = module.symbols.clone();

        // TODO Add void type
        let return_type = module.gen_type(Some(t,),);
        let args = if let Some(a,) = a {
            a.iter()
                .map(|p| match p {
                    FuncParam::Single(n, t,) => {
                        (n.clone(), true, module.gen_type(Some(t.clone(),),),)
                    }
                    FuncParam::Array(n, t,) => {
                        (n.clone(), false, module.gen_array_type(t.clone(),),)
                    }
                },)
                .collect::<Vec<_,>>()
        } else {
            Vec::new()
        };
        let function_type = LLVMFunctionType(
            return_type,
            args.iter().map(|a| a.2,).collect::<Vec<_,>>().as_mut_ptr(),
            args.len() as u32,
            0,
        );

        let value =
            LLVMAddFunction(module.module, as_str!(name), function_type,);

        for (i, e,) in args.iter().enumerate() {
            match e.1 {
                true => {
                    let fn_param = LLVMGetParam(value, i as u32,);
                    let new_symbol = Symbol::Variable(fn_param,);
                    symbols
                        .entry(e.0.clone(),)
                        .or_insert(Vec::new(),)
                        .push(new_symbol,);
                }
                false => {
                    let fn_param = LLVMGetParam(value, i as u32,);
                    let new_symbol = Symbol::ArrayRef(fn_param,);
                    symbols
                        .entry(e.0.clone(),)
                        .or_insert(Vec::new(),)
                        .push(new_symbol,);
                }
            }
        }

        Function {
            module: &module,
            symbols,
            value,
        }
    }
}

impl Module {
    unsafe fn new(context: LLVMContextRef, name: String,) -> Module {
        let module = LLVMModuleCreateWithNameInContext(
            name.as_ptr() as *const i8,
            context,
        );
        let builder = LLVMCreateBuilderInContext(context,);
        let symbols: HashMap<String, Vec<Symbol,>,> = HashMap::new();

        Module {
            module,
            context,
            symbols,
            builder,
        }
    }

    unsafe fn gen_type(self: &Module, t: Option<Type,>,) -> LLVMTypeRef {
        match t {
            Some(Type::Bool,) => LLVMInt1TypeInContext(self.context,),
            Some(Type::Int,) => LLVMInt32TypeInContext(self.context,),
            Some(Type::Str,) => panic!("Do not use gen_type with Strings!"),
            None => LLVMVoidTypeInContext(self.context,),
        }
    }

    unsafe fn gen_array_type(self: &Module, t: Type,) -> LLVMTypeRef {
        match t {
            Type::Bool => {
                LLVMPointerType(LLVMInt1TypeInContext(self.context,), 0,)
            }
            Type::Int => {
                LLVMPointerType(LLVMInt64TypeInContext(self.context,), 0,)
            }
            Type::Str => panic!("Do not use gen_array_type with Strings!"),
        }
    }

    unsafe fn global_add_variable(
        self: &mut Module,
        name: String,
        t: Type,
        expr: Option<Box<Expr,>,>,
    ) {
        let t = &self.gen_type(Some(t,),);
        let decl = LLVMAddGlobal(self.module, *t, as_str!(name),);
        if let Some(e,) = expr {
            let b = *e;
            if let Expr::Number(v,) = b {
                LLVMSetInitializer(decl, LLVMConstInt(*t, v as u64, 1,),);
            }
        } else {
            panic!("Cannot initialize global value with non-const expresion!");
        }
        let new_symbol = Symbol::Variable(decl,);
        self.symbols
            .entry(name,)
            .or_insert(Vec::new(),)
            .push(new_symbol,);
    }

    unsafe fn global_add_array(
        self: &mut Module,
        n: String,
        t: Type,
        s: u64,
        e: Option<Vec<Box<Expr,>,>,>,
    ) {
        let t = self.gen_type(Some(t,),);
        let array_type = LLVMArrayType(t, s as u32,);
        let decl = LLVMAddGlobal(self.module, array_type, as_str!(n),);
        if let Some(e,) = e {
            LLVMSetInitializer(decl, gen_initial_array(t, e,),);
        }
        let new_symbol = Symbol::Array(s as u32, decl,);
        self.symbols
            .entry(n,)
            .or_insert(Vec::new(),)
            .push(new_symbol,);
    }

    unsafe fn global_add_func(
        self: &mut Module,
        n: String,
        t: Option<Type,>,
        a: Option<Vec<FuncParam,>,>,
        b: Block,
    ) {
        let new_symbol = Symbol::Func(n.to_string(),);
        self.symbols
            .entry(n.to_string(),)
            .or_insert(Vec::new(),)
            .push(new_symbol,);

        let function = match t {
            Some(t,) => Function::new(&self, n.to_string(), t, a,),
            _ => Function::new(self, n.to_string(), Type::Int, a,),
        };

        Scope::new(&function, c_str!("entry"), b,);
    }
}

#[derive(Clone, Debug)]
enum Symbol {
    Variable(LLVMValueRef,),
    Array(u32, LLVMValueRef,),
    ArrayRef(LLVMValueRef,),
    Func(String,),
}

pub unsafe fn gen(decls: Vec<Decl,>) {
    let context = LLVMContextCreate();
    let mut module = Module::new(context, String::from("program",),);
    for i in decls {
        match i {
            Decl::Single(n, t, e,) => module.global_add_variable(n, t, e,),
            Decl::Array(n, t, s, e,) => module.global_add_array(n, t, s, e,),
            Decl::Func(n, t, a, b,) => module.global_add_func(n, t, a, b,),
        }
    }

    LLVMDumpModule(module.module,);
    LLVMPrintModuleToFile(module.module, c_str!("test.ll"), mm_str!("idk"),);
    LLVMContextDispose(context,);
}
