use super::{
    super::ast::Type,
    symbol_table::{Symbol, SymbolTable},
};
use llvm::{core::*, *};
use std::ffi::CString;

#[derive(Clone)]
pub struct Context {
    pub symbol_table: SymbolTable,
    pub module: *mut LLVMModule,
    pub context: *mut LLVMContext,
    pub builder: *mut LLVMBuilder,
    pub actual_function: Option<(*mut LLVMValue, *mut LLVMBasicBlock)>, // (function, entry)
    pub actual_loop: Option<(*mut LLVMBasicBlock, *mut LLVMBasicBlock)>, // (merge, predicate)
}

impl Context {
    pub unsafe fn new() -> Context {
        let context = LLVMContextCreate();

        Context {
            symbol_table: SymbolTable::new(),
            module: LLVMModuleCreateWithName(as_str!("program")),
            context,
            actual_function: None,
            builder: LLVMCreateBuilderInContext(context),
            actual_loop: None,
        }
    }

    pub unsafe fn declare_printf_scanf(self: &mut Self) {
        let format_int = LLVMConstString(as_str!("%d"), 3, 1);
        let format_str = LLVMConstString(as_str!("%s"), 3, 1);

        self.symbol_table
            .set("0format_int", Symbol::Variable(format_int, Type::Str))
            .unwrap();

        self.symbol_table
            .set("0format_str", Symbol::Variable(format_str, Type::Str))
            .unwrap();

        let int8_type = LLVMInt8TypeInContext(self.context);
        let int32_type = LLVMInt32TypeInContext(self.context);
        let mut args = [LLVMPointerType(int8_type, 0)];
        let fn_type = LLVMFunctionType(int32_type, args.as_mut_ptr(), 1, 1);

        let printf_fn =
            LLVMAddFunction(self.module, as_str!("printf"), fn_type);
        let scanf_fn = LLVMAddFunction(self.module, as_str!("scanf"), fn_type);

        self.symbol_table
            .set(
                "0printf",
                Symbol::Func(printf_fn, (Type::Int, vec![Type::Str])),
            )
            .unwrap();

        self.symbol_table
            .set("0scanf", Symbol::Func(scanf_fn, (Type::Int, vec![])))
            .unwrap();
    }
}
