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

pub unsafe fn gen(decls: Vec<Decl>) {
    let mut context = context::Context::new();
    context.declare_printf_scanf();
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
