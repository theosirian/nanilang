use super::symbol_table::SymbolTable;
use llvm::{core::*, *};
use std::ffi::CString;

#[derive(Clone)]
pub struct Context {
    pub symbol_table: SymbolTable,
    pub module: *mut LLVMModule,
    pub context: *mut LLVMContext,
    pub builder: *mut LLVMBuilder,
    pub actual_function: Option<*mut LLVMValue>,
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
        }
    }
}
