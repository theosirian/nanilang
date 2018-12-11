use super::{super::ast::*, context::*, symbol_table::*};
use llvm::{core::*, *};
use std::ffi::CString;

pub type SemanticError = (String, Location);

pub trait Emit<T> {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<T, SemanticError>;
}

impl Emit<*mut LLVMType> for Type {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<*mut LLVMType, SemanticError> {
        match self {
            Type::Int => Ok(LLVMInt64TypeInContext(context.context)),
            Type::Bool => Ok(LLVMInt1TypeInContext(context.context)),
            Type::Void => Ok(LLVMVoidTypeInContext(context.context)),
            Type::Str => panic!("Not implemented"),
            Type::Agg(type_of) => {
                Ok(LLVMPointerType(type_of.emit(context)?, 0))
            }
        }
    }
}

impl Emit<(*mut LLVMValue, Type)> for Variable {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(*mut LLVMValue, Type), SemanticError> {
        let builder = context.builder;
        match self {
            Variable::Single(identifier, location) => {
                if let Ok(value) = context.symbol_table.get(identifier) {
                    match value {
                        Symbol::Variable(value, type_of)
                        | Symbol::Array(value, type_of) => {
                            Ok((*value, type_of.clone()))
                        }
                        _ => Err((
                            format!("Variable {} type mismatch", identifier),
                            *location,
                        )),
                    }
                } else {
                    Err(("variabe not declared".to_string(), *location))
                }
            }
            Variable::Array(identifier, expression, location) => {
                if let Ok(value) = context.clone().symbol_table.get(identifier)
                {
                    let (index, type_of_index) = expression.emit(context)?;

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
                        _ => Err((
                            format!("Variable {} type mismatch", identifier),
                            *location,
                        )),
                    }
                } else {
                    Err((
                        format!("Variable {} not defined", identifier),
                        *location,
                    ))
                }
            }
        }
    }
}

impl Emit<(*mut LLVMValue, Type)> for Expr {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(*mut LLVMValue, Type), (String, Location)> {
        match self {
            Expr::Number(number, location) => Ok((
                LLVMConstInt(Type::Int.emit(context)?, *number, 1),
                Type::Int,
            )),
            Expr::StringLitteral(string, location) => Ok((
                LLVMBuildGlobalStringPtr(
                    context.builder,
                    as_str!(string),
                    as_str!("string"),
                ),
                Type::Str,
            )),
            Expr::True(location) => {
                Ok((LLVMConstInt(Type::Bool.emit(context)?, 1, 1), Type::Bool))
            }
            Expr::False(location) => {
                Ok((LLVMConstInt(Type::Bool.emit(context)?, 0, 1), Type::Bool))
            }
            Expr::Variable(var, location) => {
                let (ptr_var, type_of) = var.emit(context)?;

                match type_of {
                    Type::Str => Ok((ptr_var, type_of)),
                    _ => Ok((
                        LLVMBuildLoad(
                            context.builder,
                            ptr_var,
                            as_str!("var_load"),
                        ),
                        type_of,
                    )),
                }
            }
            Expr::Call(identifier, params, location) => {
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
                                            match param.emit(context) {
                                                Ok((value, type_of)) => {
                                                    //if type_of == param_expected_type {
                                                    //    Err(("Parametro diferente do esperado", *location))
                                                    //}
                                                    // else { Ok(value) },
                                                    Ok(value)
                                                }
                                                Err(e) => Err(e),
                                            }
                                        })
                                        .collect::<Result<Vec<*mut LLVMValue>, _>>()?
                                        .as_mut_ptr(),
                                    params.len() as u32,
                                    as_str!("call"),
                                ),
                                function_signature.0,
                            ))
                        }
                        _ => Err(("Type mismatch".to_string(), *location)),
                    }
                } else {
                    Err(("Identifier not declared".to_string(), *location))
                }
            }
            Expr::Op(lhs, op, rhs, location) => {
                let builder = context.builder;
                let (lhs, type_of_lhs) = lhs.emit(context)?;
                let (rhs, type_of_rhs) = rhs.emit(context)?;
                let mut type_of_result;
                let value = match op {
                    Opcode::Add => {
                        if type_of_lhs != Type::Int {
                            return Err((
                                "Lado esquerda da soma não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        if type_of_rhs != Type::Int {
                            return Err((
                                "Lado direito da soma não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        type_of_result = Type::Int;
                        LLVMBuildAdd(builder, lhs, rhs, as_str!("add_result"))
                    }
                    Opcode::Sub => {
                        if type_of_lhs != Type::Int {
                            return Err((
                                "Lado esquerda da subtração não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        if type_of_rhs != Type::Int {
                            return Err((
                                "Lado direito da subtração não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        type_of_result = Type::Int;
                        LLVMBuildSub(builder, lhs, rhs, as_str!("sub_result"))
                    }
                    Opcode::Div => {
                        if type_of_lhs != Type::Int {
                            return Err((
                                "Lado esquerda da divisão não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        if type_of_rhs != Type::Int {
                            return Err((
                                "Lado direito da divisão não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        type_of_result = Type::Int;

                        LLVMBuildUDiv(builder, lhs, rhs, as_str!("div_result"))
                    }
                    Opcode::Mul => {
                        if type_of_lhs != Type::Int {
                            return Err(("Lado esquerda da multiplicação não é inteiro".to_string(), *location));
                        }
                        if type_of_rhs != Type::Int {
                            return Err(("Lado direito da multiplicação não é inteiro".to_string(), *location));
                        }
                        type_of_result = Type::Int;

                        LLVMBuildMul(builder, lhs, rhs, as_str!("mul_result"))
                    }
                    Opcode::And => {
                        if type_of_lhs != Type::Bool {
                            return Err(("Lado esquerda da multiplicação não é booleano".to_string(), *location));
                        }
                        if type_of_rhs != Type::Bool {
                            return Err(("Lado direito da multiplicação não é booleano".to_string(), *location));
                        }
                        type_of_result = Type::Bool;

                        LLVMBuildAnd(builder, lhs, rhs, as_str!("and_result"))
                    }
                    Opcode::Or => {
                        if type_of_lhs != Type::Bool {
                            return Err(("Lado esquerda da multiplicação não é booleano".to_string(), *location));
                        }
                        if type_of_rhs != Type::Bool {
                            return Err(("Lado direito da multiplicação não é booleano".to_string(), *location));
                        }
                        type_of_result = Type::Bool;

                        LLVMBuildOr(builder, lhs, rhs, as_str!("or_result"))
                    }
                    Opcode::Mod => {
                        if type_of_lhs != Type::Int {
                            return Err((
                                "Lado esquerda do modulo não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        if type_of_rhs != Type::Int {
                            return Err((
                                "Lado direito do modulo não é inteiro"
                                    .to_string(),
                                *location,
                            ));
                        }
                        type_of_result = Type::Int;

                        LLVMBuildURem(builder, lhs, rhs, as_str!("mod_result"))
                    }
                    Opcode::Lesser
                    | Opcode::LesserOrEqual
                    | Opcode::Greater
                    | Opcode::GreaterOrEqual
                    | Opcode::Equal
                    | Opcode::Different => {
                        if type_of_lhs != type_of_rhs {
                            return Err((
                                "Lado esquerda da comparação não é do mesmo tipo que o direito"
                                    .to_string(),
                                *location,
                            ));
                        }
                        type_of_result = Type::Bool;
                        LLVMBuildICmp(
                            context.builder,
                            op.pred(),
                            lhs,
                            rhs,
                            as_str!("cmp"),
                        )
                    }
                    _ => panic!("Not implemented"),
                };
                Ok((value, type_of_result)) // FIXME type_of depend on the operand
            }
            Expr::Right(op, expression, location) => {
                let builder = context.builder;
                let (expression, type_of) = expression.emit(context)?;
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
            Expr::Ternary(_predicate, _then, _else, _location) => {
                panic!("Not implemented yet")
            }
        }
    }
}

impl Emit<()> for Stmt {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(), (String, Location)> {
        let builder = context.builder;
        match self {
            Stmt::Attr(var, expression, location) => {
                let (ptr_var, type_of) = var.emit(context)?;
                let (expression, type_of_expression) =
                    expression.emit(context)?;
                if type_of_expression != type_of {
                    return Err((
                        "Atribuição inválida".to_string(),
                        *location,
                    ));
                }

                LLVMBuildStore(builder, expression, ptr_var);
                Ok(())
            }
            Stmt::Call(identifier, expressions, location) => {
                Expr::Call(
                    identifier.to_string(),
                    expressions.clone(),
                    *location,
                )
                .emit(context)?;
                Ok(())
            }
            Stmt::For(init, predicate, step, block, location) => {
                init.emit(context)?;
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

                context.symbol_table.initialize_scope();
                context
                    .symbol_table
                    .set("0loop_merge", Symbol::JumpBlock(block_merge))
                    .unwrap();
                context
                    .symbol_table
                    .set("0loop_step", Symbol::JumpBlock(block_step))
                    .unwrap();

                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_predicate);
                let (predicate, type_of_predicate) = predicate.emit(context)?;
                if type_of_predicate != Type::Bool {
                    return Err((
                        "Predicado não é booleano".to_string(),
                        *location,
                    ));
                }
                LLVMBuildCondBr(
                    context.builder,
                    predicate,
                    block_for,
                    block_merge,
                );

                LLVMPositionBuilderAtEnd(context.builder, block_for);
                block.emit(context)?;
                LLVMBuildBr(context.builder, block_step);
                LLVMPositionBuilderAtEnd(context.builder, block_step);
                step.emit(context)?;
                LLVMBuildBr(context.builder, block_predicate);
                context.symbol_table.kill_scope();

                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
            }
            Stmt::While(predicate, block, location) => {
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

                context.symbol_table.initialize_scope();
                context
                    .symbol_table
                    .set("0loop_merge", Symbol::JumpBlock(block_merge))
                    .unwrap();
                context
                    .symbol_table
                    .set("0loop_step", Symbol::JumpBlock(block_predicate))
                    .unwrap();

                LLVMBuildBr(context.builder, block_predicate);

                LLVMPositionBuilderAtEnd(context.builder, block_predicate);
                let (predicate, type_of_predicate) = predicate.emit(context)?;

                if type_of_predicate != Type::Bool {
                    return Err((
                        "Predicado não é booleano".to_string(),
                        *location,
                    ));
                }
                LLVMBuildCondBr(
                    context.builder,
                    predicate,
                    block_while,
                    block_merge,
                );

                LLVMPositionBuilderAtEnd(context.builder, block_while);
                block.emit(context)?;
                LLVMBuildBr(context.builder, block_predicate);
                context.symbol_table.kill_scope();

                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
            }
            Stmt::Stop(location) => {
                if let Ok(merge) = context.symbol_table.get("0loop_merge") {
                    if let Symbol::JumpBlock(merge) = merge {
                        LLVMBuildBr(context.builder, *merge);
                        Ok(())
                    } else {
                        Err(("Impossibru!!".to_string(), *location))
                    }
                } else {
                    Err(("Stop not in a loop".to_string(), *location))
                }
            }
            Stmt::Skip(location) => {
                if let Ok(predicate) = context.symbol_table.get("0loop_step") {
                    if let Symbol::JumpBlock(predicate) = predicate {
                        LLVMBuildBr(context.builder, *predicate);
                        Ok(())
                    } else {
                        Err(("Impossibru!!".to_string(), *location))
                    }
                } else {
                    Err(("Skip not in a loop".to_string(), *location))
                }
            }
            Stmt::Return(expression, location) => {
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
            Stmt::If(expression, block, elifs, else_block, location) => {
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
                        context.symbol_table.initialize_scope();
                        else_block.emit(context).unwrap();
                        context.symbol_table.kill_scope();
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
                        context.symbol_table.initialize_scope();
                        actual_block.1.emit(context).unwrap();
                        context.symbol_table.kill_scope();
                        LLVMBuildBr(context.builder, block_merge);

                        block_elif_predicate
                    },
                );

                LLVMPositionBuilderAtEnd(context.builder, block_if_predicate);
                let (cmp_expression, type_of) = expression.emit(context)?;
                if type_of != Type::Bool {
                    return Err((
                        "Predicado não é booleano".to_string(),
                        *location,
                    ));
                }

                LLVMBuildCondBr(
                    context.builder,
                    cmp_expression,
                    block_if_then,
                    block_else_to_jump,
                );
                LLVMPositionBuilderAtEnd(context.builder, block_if_then);
                context.symbol_table.initialize_scope();
                block.emit(context).unwrap();
                context.symbol_table.kill_scope();
                LLVMBuildBr(context.builder, block_merge);
                LLVMPositionBuilderAtEnd(context.builder, block_merge);

                Ok(())
            }
            Stmt::Write(list_expr, location) => {
                let printf_fn =
                    match context.symbol_table.get("0printf").unwrap() {
                        Symbol::Func(value, _type_of) => value,
                        _ => panic!("What"),
                    };

                let format_str = LLVMBuildGlobalStringPtr(
                    context.builder,
                    as_str!("%s"),
                    as_str!("format_str"),
                );

                let format_int = LLVMBuildGlobalStringPtr(
                    context.builder,
                    as_str!("%d"),
                    as_str!("format_int"),
                );

                let format_barra_n = LLVMBuildGlobalStringPtr(
                    context.builder,
                    as_str!("\n"),
                    as_str!("barra_n"),
                );

                list_expr.iter().for_each(|expr| {
                    let (value, type_of) =
                        expr.emit(&mut context.clone()).unwrap();

                    match type_of {
                        Type::Int | Type::Bool => {
                            LLVMBuildCall(
                                context.builder,
                                *printf_fn,
                                vec![format_int, value].as_mut_ptr(),
                                2,
                                as_str!("call_write"),
                            );
                        }
                        Type::Str => {
                            LLVMBuildCall(
                                context.builder,
                                *printf_fn,
                                vec![format_str, value].as_mut_ptr(),
                                2,
                                as_str!("call_write"),
                            );
                        }
                        _ => panic!("Not implemented"),
                    }
                });
                LLVMBuildCall(
                    context.builder,
                    *printf_fn,
                    vec![format_barra_n].as_mut_ptr(),
                    1,
                    as_str!("call_write"),
                );

                Ok(())
            }
            Stmt::Read(variable, location) => {
                let format_int = LLVMBuildGlobalStringPtr(
                    context.builder,
                    as_str!("%d"),
                    as_str!("format_int"),
                );

                let scanf_fn = match context.symbol_table.get("0scanf").unwrap()
                {
                    Symbol::Func(value, _type_of) => value,
                    _ => panic!("What"),
                };

                let (variable_ptr, type_of) =
                    variable.emit(&mut context.clone())?;

                LLVMBuildCall(
                    context.builder,
                    *scanf_fn,
                    vec![format_int, variable_ptr].as_mut_ptr(),
                    2,
                    as_str!("call_read"),
                );

                Ok(())
            }
            _ => panic!("Not implemented"),
        }
    }
}

impl Emit<()> for Decl {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(), (String, Location)> {
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
                Decl::Single(identifier, type_of, expression, location) => {
                    match type_of {
                        Type::Str => {
                            if let Some(expression) = expression {
                                let (string, _) = expression.emit(context)?;

                                if context
                                    .symbol_table
                                    .set(
                                        identifier,
                                        Symbol::Variable(
                                            string,
                                            type_of.clone(),
                                        ),
                                    )
                                    .is_err()
                                {
                                    return Err((
                                        format!(
                                            "Identifier {} already declared",
                                            identifier
                                        ),
                                        *location,
                                    ));
                                }

                                Ok(())
                            } else {
                                Err((
                                    "String must be initialized".to_string(),
                                    *location,
                                ))
                            }
                        }
                        _ => {
                            let ptr_vlr = LLVMBuildAlloca(
                                alloc_builder,
                                type_of.emit(context).unwrap(),
                                as_str!(identifier),
                            );

                            if context
                                .symbol_table
                                .set(
                                    identifier,
                                    Symbol::Variable(ptr_vlr, type_of.clone()),
                                )
                                .is_err()
                            {
                                return Err((
                                    format!(
                                        "Identifier {} already declared",
                                        identifier
                                    ),
                                    *location,
                                ));
                            }

                            if let Some(expression) = expression {
                                let (expression, type_of_expression) =
                                    expression.emit(context).unwrap();
                                LLVMBuildStore(builder, expression, ptr_vlr);
                                Ok(())
                            } else {
                                Ok(())
                            }
                        }
                    }
                }
                Decl::Array(
                    identifier,
                    type_of,
                    size,
                    list_expression,
                    location,
                ) => {
                    let (expression_size, _) =
                        Expr::Number(*size, *location).emit(context).unwrap();

                    let ptr_vlr = LLVMBuildArrayAlloca(
                        context.builder,
                        type_of.emit(context).unwrap(),
                        expression_size,
                        as_str!(identifier),
                    );
                    if context
                        .symbol_table
                        .set(
                            identifier,
                            Symbol::Array(ptr_vlr, type_of.clone()),
                        )
                        .is_err()
                    {
                        return Err((
                            format!(
                                "Identifier {} already declared",
                                identifier
                            ),
                            *location,
                        ));
                    }

                    // TODO Initialization

                    Ok(())
                }
                _ => panic!("Function not expected".to_string()),
            }
        } else {
            // When global
            match self {
                Decl::Single(identifier, type_of, expression, location) => {
                    let decl = LLVMAddGlobal(
                        context.module,
                        type_of.emit(context).unwrap(),
                        as_str!(identifier),
                    );

                    if context
                        .symbol_table
                        .set(
                            identifier,
                            Symbol::Variable(decl, type_of.clone()),
                        )
                        .is_err()
                    {
                        return Err((
                            format!(
                                "Identifier {} already declared",
                                identifier
                            ),
                            *location,
                        ));
                    }

                    if let Some(expression) = expression {
                        let (value, type_of) =
                            expression.emit(context).unwrap();

                        LLVMSetInitializer(decl, value);
                    }

                    Ok(())
                }
                Decl::Array(
                    identifier,
                    type_of,
                    size,
                    list_expression,
                    location,
                ) => {
                    let array_type = LLVMArrayType(
                        type_of.emit(context).unwrap(),
                        *size as u32,
                    );

                    let decl = LLVMAddGlobal(
                        context.module,
                        array_type,
                        as_str!(identifier),
                    );

                    if context
                        .symbol_table
                        .set(identifier, Symbol::Array(decl, type_of.clone()))
                        .is_err()
                    {
                        return Err((
                            format!(
                                "Identifier {} already declared",
                                identifier
                            ),
                            *location,
                        ));
                    }

                    // TODO Initialization

                    Ok(())
                }
                Decl::Func(
                    identifier,
                    return_type,
                    vec_params,
                    block,
                    location,
                ) => {
                    let vec_params = vec_params.clone().unwrap_or_default();

                    let mut args = vec_params
                        .iter()
                        .map(|param| match param {
                            FuncParam::Single(_, type_of, _) => {
                                type_of.emit(context).unwrap()
                            }
                            FuncParam::Array(_, type_of, _) => {
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

                    if context
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
                                            FuncParam::Single( _, type_of, _,)
                                            | FuncParam::Array(_, type_of, _) => type_of.clone(),
                                        })
                                        .collect::<Vec<_>>(),
                                ),
                            ),
                        )
                        .is_err()
                    {
                        return Err((
                            format!(
                                "Identifier {} already declared",
                                identifier
                            ),
                            *location,
                        ));
                    }

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
                            FuncParam::Single(
                                identifier,
                                type_of,
                                location,
                            ) => {
                                let ptr_vlr = LLVMBuildAlloca(
                                    context.builder,
                                    type_of.emit(context).unwrap(),
                                    as_str!(identifier),
                                );
                                context
                                    .symbol_table
                                    .set(
                                        &identifier,
                                        Symbol::Variable(
                                            ptr_vlr,
                                            type_of.clone(),
                                        ),
                                    )
                                    .unwrap();

                                LLVMBuildStore(
                                    context.builder,
                                    function_param,
                                    ptr_vlr,
                                );
                            }
                            FuncParam::Array(identifier, type_of, location) => {
                                let ptr_vlr = LLVMBuildAlloca(
                                    context.builder,
                                    type_of.emit(context).unwrap(),
                                    as_str!(identifier),
                                );
                                context
                                    .symbol_table
                                    .set(
                                        &identifier,
                                        Symbol::Array(ptr_vlr, type_of.clone()),
                                    )
                                    .unwrap();

                                LLVMBuildStore(
                                    context.builder,
                                    function_param,
                                    ptr_vlr,
                                );
                            }
                        }
                    });

                    block.emit(context)?;

                    context.symbol_table.kill_scope();

                    if !return_type.is_some() {
                        LLVMBuildRetVoid(context.builder);
                    }

                    context.actual_function = None;
                    Ok(())
                }
            }
        }
    }
}

impl Emit<()> for Block {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(), (String, Location)> {
        for decl in self.decl.iter() {
            decl.emit(context)?;
        }
        for command in self.commands.iter() {
            command.emit(context)?;
        }

        Ok(())
    }
}

impl Emit<()> for Either<Stmt, Block> {
    unsafe fn emit(
        self: &Self,
        context: &mut Context,
    ) -> Result<(), (String, Location)> {
        match self {
            Either::Left(stmt) => stmt.emit(context)?,
            Either::Right(block) => block.emit(context)?,
        };

        Ok(())
    }
}
