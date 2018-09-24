use ast::*;

use llvm::core::*;
use llvm::prelude::*;

/// Generate the initialization of a array considering a type
/// TODO Check the types of the elements if its match the type specified
pub unsafe fn gen_initial_array(
    t: LLVMTypeRef,
    e: Vec<Box<Expr,>,>,
) -> LLVMValueRef {
    let mut args = e
        .iter()
        .map(|b| match **b {
            Expr::Number(e,) => LLVMConstInt(t, e, 1,),
            Expr::True => LLVMConstInt(t, 1, 1,),
            Expr::False => LLVMConstInt(t, 0, 1,),
            _ => panic!(
                "Cannot initialize global value with non-const expresion!"
            ),
        },)
        .collect::<Vec<_,>>();
    LLVMConstArray(t, args.as_mut_ptr(), args.len() as u32,)
}
