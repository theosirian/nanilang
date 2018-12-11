use codespan::CodeMap;
use codespan_reporting::{
    emit,
    termcolor::{ColorChoice, StandardStream},
    Diagnostic, Label,
};
use std::{ffi::CString, process::exit};

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

pub unsafe fn gen(decls: Vec<Decl>, code_map: &CodeMap) {
    let mut context = context::Context::new();
    context.declare_printf_scanf();
    for i in decls {
        let writer = StandardStream::stderr(ColorChoice::Always);
        if let Err((msg, span)) = i.emit(&mut context) {
            let diagnostic = Diagnostic::new_error(msg);
            let label = Label::new_primary(span);
            emit(writer, &code_map, &diagnostic.with_label(label)).unwrap();
            exit(127);
        }
    }
    LLVMPrintModuleToFile(
        context.module,
        as_str!("test.ll"),
        as_str!("idk") as *mut *mut i8,
    );
    LLVMContextDispose(context.context);
}
