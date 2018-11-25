use super::{super::ast::*, context::*, symbol_table::*};
use llvm::{core::*, *};
use std::ffi::CString;

pub trait Emit<T> {
    unsafe fn emit(self: &Self, context: &mut Context) -> Result<T, String>;
}

impl Emit<*mut LLVMType> for Type {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<*mut LLVMType, String> {
        match self {
            Type::Int => Ok(LLVMInt64TypeInContext(context.context)),
            Type::Bool => Ok(LLVMInt1TypeInContext(context.context)),
            Type::Void => Ok(LLVMVoidTypeInContext(context.context)),
            Type::Str => panic!("Not implemented"),
        }
    }
}

impl Emit<*mut LLVMValue> for Variable {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<*mut LLVMValue, String> {
        let builder = context.builder;
        match self {
            Variable::Single(identifier) => {
                if let Ok(value) = context.symbol_table.get(identifier) {
                    match value {
                        Symbol::Variable(value) => Ok(*value),
                        _ => panic!("Variable type mismatch"),
                    }
                } else {
                    Err(String::from("variabe not declared"))
                }
            }
            Variable::Array(identifier, expression) => {
                if let Ok(value) = context.clone().symbol_table.get(identifier)
                {
                    let index = expression.emit(context).unwrap();

                    match value {
                        Symbol::ArrayRef(value) | Symbol::Array(_, value) => {
                            Ok(LLVMBuildInBoundsGEP(
                                builder,
                                *value,
                                [index].as_mut_ptr(),
                                1,
                                as_str!("ptr_value"),
                            ))
                        }
                        _ => Err("Variable type mismatch".to_string()),
                    }
                } else {
                    Err("Variable not defined".to_string())
                }
            }
        }
    }
}

impl Emit<*mut LLVMValue> for Expr {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<*mut LLVMValue, String> {
        match self {
            Expr::Number(number) => {
                Ok(LLVMConstInt(Type::Int.emit(context).unwrap(), *number, 1))
            }
            Expr::True => {
                Ok(LLVMConstInt(Type::Bool.emit(context).unwrap(), 1, 1))
            }
            Expr::False => {
                Ok(LLVMConstInt(Type::Bool.emit(context).unwrap(), 0, 1))
            }
            Expr::Variable(var) => {
                let ptr_var = var.emit(context).unwrap();

                Ok(LLVMBuildLoad(context.builder, ptr_var, as_str!("var_load")))
            }
            Expr::Call(identifier, params) => {
                let builder = context.builder;
                if let Ok(function) =
                    context.clone().symbol_table.get(identifier)
                {
                    match function {
                        // TODO Put function value in symbols table
                        Symbol::Func(function) => {
                            let function = LLVMGetNamedFunction(
                                context.module,
                                as_str!(function),
                            );
                            let params = params.clone().unwrap_or_default();

                            Ok(LLVMBuildCall(
                                builder,
                                function,
                                params
                                    .iter()
                                    .map(|param| param.emit(context).unwrap())
                                    .collect::<Vec<*mut LLVMValue>>()
                                    .as_mut_ptr(),
                                params.len() as u32,
                                as_str!("call"),
                            ))
                        }
                        _ => Err("Type mismatch".to_string()),
                    }
                } else {
                    Err("Identifier not declared".to_string())
                }
            }
            Expr::Op(lhs, op, rhs) => {
                let builder = context.builder;
                let lhs = lhs.emit(context).unwrap();
                let rhs = rhs.emit(context).unwrap();
                let value = match op {
                    Opcode::Add => {
                        LLVMBuildAdd(builder, lhs, rhs, as_str!("add_result"))
                    }
                    Opcode::Sub => {
                        LLVMBuildSub(builder, lhs, rhs, as_str!("sub_result"))
                    }
                    Opcode::Div => {
                        LLVMBuildUDiv(builder, lhs, rhs, as_str!("div_result"))
                    }
                    Opcode::Mul => {
                        LLVMBuildMul(builder, lhs, rhs, as_str!("mul_result"))
                    }
                    Opcode::Mod => panic!("Não encontrei a chamada do modulo"),
                    Opcode::Lesser
                    | Opcode::LesserOrEqual
                    | Opcode::Greater
                    | Opcode::GreaterOrEqual
                    | Opcode::Equal
                    | Opcode::Different => LLVMBuildICmp(
                        context.builder,
                        op.pred(),
                        lhs,
                        rhs,
                        as_str!("cmp"),
                    ),
                    _ => panic!("Not implemented"),
                };
                Ok(value)
            }
            Expr::Right(op, expression) => {
                let builder = context.builder;
                let expression = expression.emit(context).unwrap();
                let value = match op {
                    Opcode::Not => {
                        LLVMBuildNot(builder, expression, as_str!("not_result"))
                    }
                    Opcode::Negative => LLVMBuildNeg(
                        builder,
                        expression,
                        as_str!("negation_result"),
                    ),
                    _ => panic!("Should not do this"),
                };
                Ok(value)
            }
            Expr::Ternary(_, _, _) => panic!("Not implemented yet"),
        }
    }
}

impl Emit<()> for Stmt {
    unsafe fn emit(self: &Self, context: &mut Context) -> Result<(), String> {
        let builder = context.builder;
        match self {
            Stmt::Attr(var, expression) => {
                let ptr_var = var.emit(context).unwrap();
                let expression = expression.emit(context).unwrap();

                LLVMBuildStore(builder, expression, ptr_var);
                Ok(())
            }
            Stmt::Call(identifier, expressions) => {
                Expr::Call(identifier.to_string(), expressions.clone())
                    .emit(context)
                    .unwrap();
                Ok(())
            }
            Stmt::For(init, predicate, step, block) => {
                init.emit(context).unwrap();
                let block_predicate = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("predicate_for"),
                );
                let block_for = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("block_for"),
                );
                let block_step = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("block_step"),
                );
                let block_merge = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("merge_for"),
                );
                context.actual_loop = Some((block_merge, block_step));

                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_predicate);
                LLVMBuildCondBr(
                    context.builder,
                    predicate.emit(context).unwrap(),
                    block_for,
                    block_merge,
                );

                LLVMPositionBuilderAtEnd(context.builder, block_for);
                block.emit(context).unwrap();
                LLVMBuildBr(context.builder, block_step);
                LLVMPositionBuilderAtEnd(context.builder, block_step);
                step.emit(context).unwrap();
                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
            }
            Stmt::While(predicate, block) => {
                let block_predicate = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("predicate_for"),
                );
                let block_while = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("block_for"),
                );
                let block_merge = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("merge_for"),
                );
                context.actual_loop = Some((block_merge, block_predicate));

                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_predicate);
                LLVMBuildCondBr(
                    context.builder,
                    predicate.emit(context).unwrap(),
                    block_while,
                    block_merge,
                );

                LLVMPositionBuilderAtEnd(context.builder, block_while);
                block.emit(context).unwrap();
                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
            }
            Stmt::Stop => {
                if let Some((merge, _)) = context.actual_loop {
                    LLVMBuildBr(context.builder, merge);
                    Ok(())
                } else {
                    Err("Stop not in a loop".to_string())
                }
            }
            Stmt::Skip => {
                if let Some((_, predicate)) = context.actual_loop {
                    LLVMBuildBr(context.builder, predicate);
                    Ok(())
                } else {
                    Err("Skip not in a loop".to_string())
                }
            }
            Stmt::Return(expression) => {
                if let Some(expression) = expression {
                    LLVMBuildRet(
                        context.builder,
                        expression.emit(context).unwrap(),
                    );
                    Ok(())
                } else {
                    LLVMBuildRetVoid(context.builder);
                    Ok(())
                }
            }
            _ => panic!("Not implemented"),
        }
    }
}

impl Emit<()> for Decl {
    unsafe fn emit(self: &Self, context: &mut Context) -> Result<(), String> {
        if context.actual_function.is_some() {
            // When local
            let alloc_builder = LLVMCreateBuilderInContext(context.context);
            let first_intr =
                LLVMGetFirstInstruction(context.actual_function.unwrap().1);
            if !first_intr.is_null() {
                LLVMPositionBuilderBefore(alloc_builder, first_intr);
            } else {
                LLVMPositionBuilderAtEnd(
                    alloc_builder,
                    context.actual_function.unwrap().1,
                );
            }

            let builder = context.builder;
            match self {
                Decl::Single(identifier, type_of, expression) => {
                    let ptr_vlr = LLVMBuildAlloca(
                        alloc_builder,
                        type_of.emit(context).unwrap(),
                        as_str!(identifier),
                    );
                    context
                        .symbol_table
                        .set(identifier, Symbol::Variable(ptr_vlr));

                    if let Some(expression) = expression {
                        LLVMBuildStore(
                            builder,
                            expression.emit(context).unwrap(),
                            ptr_vlr,
                        );
                        Ok(())
                    } else {
                        Ok(())
                    }
                }
                _ => panic!("Not implemented!"),
            }
        } else {
            // When global
            match self {
                Decl::Single(identifier, type_of, expression) => {
                    let decl = LLVMAddGlobal(
                        context.module,
                        type_of.emit(context).unwrap(),
                        as_str!(identifier),
                    );

                    if let Some(expression) = expression {
                        LLVMSetInitializer(
                            decl,
                            expression.emit(context).unwrap(),
                        );
                        Ok(())
                    } else {
                        Ok(())
                    }
                }
                Decl::Func(identifier, return_type, vec_params, block) => {
                    let vec_params = vec_params.clone().unwrap_or_default();

                    let mut args = vec_params
                        .iter()
                        .map(|param| match param {
                            FuncParam::Single(_, type_of) => {
                                type_of.emit(context).unwrap()
                            }
                            FuncParam::Array(_, type_of) => {
                                type_of.emit(context).unwrap()
                            }
                        })
                        .collect::<Vec<_>>();

                    let function_type = LLVMFunctionType(
                        return_type
                            .clone()
                            .unwrap_or_default()
                            .emit(context)
                            .unwrap(),
                        args.as_mut_ptr(),
                        args.len() as u32,
                        false as i32,
                    );
                    let function = LLVMAddFunction(
                        context.module,
                        as_str!(identifier),
                        function_type,
                    );

                    let entry_block = LLVMAppendBasicBlockInContext(
                        context.context,
                        function,
                        as_str!("entry"),
                    );

                    context.symbol_table.initialize_scope();

                    context.actual_function = Some((function, entry_block));
                    LLVMPositionBuilderAtEnd(context.builder, entry_block);

                    vec_params.iter().enumerate().for_each(|(index, param)| {
                        let function_param =
                            LLVMGetParam(function, index as u32);

                        match param {
                            FuncParam::Single(identifier, type_of) => {
                                let ptr_vlr = LLVMBuildAlloca(
                                    context.builder,
                                    type_of.emit(context).unwrap(),
                                    as_str!(identifier),
                                );
                                context
                                    .symbol_table
                                    .set(identifier, Symbol::Variable(ptr_vlr));

                                LLVMBuildStore(
                                    context.builder,
                                    function_param,
                                    ptr_vlr,
                                );
                            }
                            FuncParam::Array(_identifier, _type_of) => {
                                panic!("Not implemented yet")
                            }
                        }
                    });

                    block.emit(context).unwrap();

                    context.symbol_table.kill_scope();

                    Ok(())
                }
                _ => panic!("Not implemented"),
            }
        }
    }
}

impl Emit<()> for Block {
    unsafe fn emit(self: &Self, context: &mut Context) -> Result<(), String> {
        context.symbol_table.initialize_scope();
        self.decl
            .iter()
            .for_each(|decl| decl.emit(context).unwrap());

        self.commands
            .iter()
            .for_each(|command| command.emit(context).unwrap());
        context.symbol_table.kill_scope();

        Ok(())
    }
}

impl Emit<()> for Either<Stmt, Block> {
    unsafe fn emit(self: &Self, context: &mut Context) -> Result<(), String> {
        match self {
            Either::Left(stmt) => stmt.emit(context).unwrap(),
            Either::Right(block) => block.emit(context).unwrap(),
        };

        Ok(())
    }
}
