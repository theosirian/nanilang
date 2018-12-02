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
            Type::Agg(_) => panic!("Not implemented"),
        }
    }
}

impl Emit<(*mut LLVMValue, Type)> for Variable {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(*mut LLVMValue, Type), String> {
        let builder = context.builder;
        match self {
            Variable::Single(identifier) => {
                if let Ok(value) = context.symbol_table.get(identifier) {
                    match value {
                        Symbol::Variable(value, type_of) => {
                            Ok((*value, type_of.clone()))
                        }
                        _ => Err(format!(
                            "Variable {} type mismatch",
                            identifier
                        )),
                    }
                } else {
                    Err("variabe not declared".to_string())
                }
            }
            Variable::Array(identifier, expression) => {
                if let Ok(value) = context.clone().symbol_table.get(identifier)
                {
                    let (index, type_of_index) =
                        expression.emit(context).unwrap();

                    match value {
                        Symbol::Array(value, type_of) => Ok((
                            LLVMBuildInBoundsGEP(
                                builder,
                                *value,
                                [index].as_mut_ptr(),
                                1,
                                as_str!("ptr_value"),
                            ),
                            type_of.clone(),
                        )),
                        _ => Err(format!(
                            "Variable {} type mismatch",
                            identifier
                        )),
                    }
                } else {
                    Err("Variable not defined".to_string())
                }
            }
        }
    }
}

impl Emit<(*mut LLVMValue, Type)> for Expr {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(*mut LLVMValue, Type), String> {
        match self {
            Expr::Number(number) => Ok((
                LLVMConstInt(Type::Int.emit(context).unwrap(), *number, 1),
                Type::Int,
            )),
            Expr::True => Ok((
                LLVMConstInt(Type::Bool.emit(context).unwrap(), 1, 1),
                Type::Bool,
            )),
            Expr::False => Ok((
                LLVMConstInt(Type::Bool.emit(context).unwrap(), 0, 1),
                Type::Bool,
            )),
            Expr::Variable(var) => {
                let (ptr_var, type_of) = var.emit(context).unwrap();

                Ok((
                    LLVMBuildLoad(
                        context.builder,
                        ptr_var,
                        as_str!("var_load"),
                    ),
                    type_of,
                ))
            }
            Expr::Call(identifier, params) => {
                let builder = context.builder;
                if let Ok(function) =
                    context.clone().symbol_table.get(identifier)
                {
                    match function {
                        // TODO Put function value in symbols table
                        Symbol::Func(function, function_signature) => {
                            let params = params.clone().unwrap_or_default();
                            let function_signature = function_signature.clone();

                            Ok((
                                LLVMBuildCall(
                                    builder,
                                    *function,
                                    params
                                        .iter()
                                        .zip(function_signature.1)
                                        .map(|(param, param_expected_type)| {
                                            let (value, type_of) =
                                                param.emit(context).unwrap();
                                            // TODO Check type_of with function_signature
                                            value
                                        })
                                        .collect::<Vec<*mut LLVMValue>>()
                                        .as_mut_ptr(),
                                    params.len() as u32,
                                    as_str!("call"),
                                ),
                                function_signature.0,
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
                let (lhs, type_of_lhs) = lhs.emit(context).unwrap();
                let (rhs, type_of_rhs) = rhs.emit(context).unwrap();
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
                Ok((value, Type::Int)) // FIXME type_of depend on the operand
            }
            Expr::Right(op, expression) => {
                let builder = context.builder;
                let (expression, type_of) = expression.emit(context).unwrap();
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
                Ok((value, Type::Int)) // FIXME type_of depend on the operand
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
                let (ptr_var, type_of) = var.emit(context).unwrap();
                let (expression, type_of_expression) =
                    expression.emit(context).unwrap();

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
                let (predicate, type_of_predicate) =
                    predicate.emit(context).unwrap();
                LLVMBuildCondBr(
                    context.builder,
                    predicate,
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

                let (predicate, type_of_predicate) =
                    predicate.emit(context).unwrap();
                LLVMPositionBuilderAtEnd(context.builder, block_predicate);
                LLVMBuildCondBr(
                    context.builder,
                    predicate,
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
                    let (expression, type_of) =
                        expression.emit(context).unwrap();
                    LLVMBuildRet(context.builder, expression);
                    Ok(())
                } else {
                    LLVMBuildRetVoid(context.builder);
                    Ok(())
                }
            }
            Stmt::If(expression, block, elifs, else_block) => {
                let block_if_predicate = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("if_predicate"),
                );
                LLVMBuildBr(context.builder, block_if_predicate);
                let block_if_then = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("if_then"),
                );
                let block_merge = LLVMAppendBasicBlockInContext(
                    context.context,
                    context.actual_function.unwrap().0,
                    as_str!("merge_if"),
                );
                let last_block = match else_block {
                    Some(else_block) => {
                        let block_if_else = LLVMAppendBasicBlockInContext(
                            context.context,
                            context.actual_function.unwrap().0,
                            as_str!("if_else"),
                        );
                        LLVMPositionBuilderAtEnd(
                            context.builder,
                            block_if_else,
                        );
                        else_block.emit(context).unwrap();
                        LLVMBuildBr(context.builder, block_merge);

                        block_if_else
                    }
                    None => block_merge,
                };
                let block_else_to_jump = elifs.iter().rev().fold(
                    last_block,
                    |last_block, actual_block| {
                        let block_elif_predicate =
                            LLVMAppendBasicBlockInContext(
                                context.context,
                                context.actual_function.unwrap().0,
                                as_str!("block_elif"),
                            );
                        let block_elif_then = LLVMAppendBasicBlockInContext(
                            context.context,
                            context.actual_function.unwrap().0,
                            as_str!("block_elif"),
                        );
                        LLVMPositionBuilderAtEnd(
                            context.builder,
                            block_elif_predicate,
                        );
                        let (elif_predicate, type_of_elif_predicate) =
                            actual_block.0.emit(context).unwrap();

                        LLVMBuildCondBr(
                            context.builder,
                            elif_predicate,
                            block_elif_then,
                            last_block,
                        );
                        LLVMPositionBuilderAtEnd(
                            context.builder,
                            block_elif_then,
                        );
                        actual_block.1.emit(context).unwrap();
                        LLVMBuildBr(context.builder, block_merge);

                        block_elif_predicate
                    },
                );

                LLVMPositionBuilderAtEnd(context.builder, block_if_predicate);
                let (cmp_expression, type_of) =
                    expression.emit(context).unwrap();
                LLVMBuildCondBr(
                    context.builder,
                    cmp_expression,
                    block_if_then,
                    block_else_to_jump,
                );
                LLVMPositionBuilderAtEnd(context.builder, block_if_then);
                block.emit(context).unwrap();
                LLVMBuildBr(context.builder, block_merge);
                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
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
                        .set(identifier, Symbol::Variable(ptr_vlr, type_of.clone()))
                        .expect("Can't set the variable, probably the variable is already declared");

                    if let Some(expression) = expression {
                        let (expression, type_of_expression) =
                            expression.emit(context).unwrap();
                        LLVMBuildStore(builder, expression, ptr_vlr);
                        Ok(())
                    } else {
                        Ok(())
                    }
                }
                Decl::Array(identifier, type_of, size, list_expression) => {
                    let (expression_size, _) =
                        Expr::Number(*size).emit(context).unwrap();

                    let ptr_vlr = LLVMBuildArrayAlloca(
                        context.builder,
                        type_of.emit(context).unwrap(),
                        expression_size,
                        as_str!(identifier),
                    );
                    context
                        .symbol_table
                        .set(identifier, Symbol::Array(ptr_vlr, type_of.clone()))
                        .expect("Can't set the variable, probably the variable is already declared");

                    // TODO Initialization

                    Ok(())
                }
                _ => Err("Function not expected".to_string()),
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

                    context
                        .symbol_table
                        .set(
                            identifier,
                            Symbol::Variable(decl, type_of.clone()),
                        )
                        .unwrap();

                    if let Some(expression) = expression {
                        let (value, type_of) =
                            expression.emit(context).unwrap();

                        LLVMSetInitializer(decl, value);
                        Ok(())
                    } else {
                        Ok(())
                    }
                }
                Decl::Array(identifier, type_of, size, list_expression) => {
                    let array_type = LLVMArrayType(
                        type_of.emit(context).unwrap(),
                        *size as u32,
                    );

                    let decl = LLVMAddGlobal(
                        context.module,
                        array_type,
                        as_str!(identifier),
                    );

                    context
                        .symbol_table
                        .set(identifier, Symbol::Array(decl, type_of.clone()))
                        .unwrap();

                    // TODO Initialization

                    Ok(())
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

                    context
                        .symbol_table
                        .set(
                            identifier,
                            Symbol::Func(
                                function,
                                (
                                    return_type.clone().unwrap_or_default(),
                                    vec_params
                                        .iter()
                                        .map(|param| match param {
                                            FuncParam::Single(_, type_of) => {
                                                type_of.clone()
                                            }
                                            FuncParam::Array(_, type_of) => {
                                                Type::Agg(Box::new(
                                                    type_of.clone(),
                                                ))
                                            }
                                        })
                                        .collect::<Vec<_>>(),
                                ),
                            ),
                        )
                        .unwrap();

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
                                    .set(identifier, Symbol::Variable(ptr_vlr, type_of.clone()))
                                    .expect("Can't set the variable, probably the variable is already declared");

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
