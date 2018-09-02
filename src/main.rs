extern crate llvm_sys as llvm;

use ast::*;
use llvm::core::*;
use llvm::prelude::*;
use std::collections::HashMap;
use std::ffi::*;

mod ast;
mod grammar;

enum Symbol {
    Variable(LLVMValueRef),
    Array(u32, LLVMValueRef),
    Func(String),
}

fn main() {
    let expr = grammar::ProgramParser::new()
        .parse(
            r#"
def hello(a, b: int): int {
    let a = 7: int;
    let b[2] = {4, 3} : int;
    read a;
    write a;
}

let global_var = 13: int;
let global_arr[2] = {0, 1}: int;

def main(): int {
    let i: int;
    let a = true: bool;
    let b = 0: int;
    let c[2] = {0, 1}: int;

    let x: bool;
    let y, z: str;
    let w, d = true: bool;
    let e, f = 0 + e, g = 2: int;
    let h[2], i[3] = { 1, 2, 3 }: int;
    let __testing = 1: int;

    e = 22 * 44 + 66;
    f = x == true ? __testing : 1 + 2;
    g = w == true ? (13 == __testing ? 0 : 1) : 1 + 2;

    a += b + 2;
    b -= 2;
    c[0] += 1;
    e *= 3;
    f /= 4;
    g %= 5;

    read a;
    read c[0];
    write 10;
    write a;
    write a, c[0];

    hello();
    hello(a);
    hello(a, b);

    if (a) {
        let b = 0: int;
        hello(b);
    } else if (b > 3) {
        hello(false);
    } else {
        hello(a);
    }

    while (true) {
        hello(i);
        skip;
    }

    for (i = 0; i < 10; i += 1) {
        hello(i);
        stop;
    }

    return;
    return 1;
    return a;
}
        "#,
        )
        .unwrap();
    println!("{:#?}", expr);

    unsafe {
        let context = LLVMContextCreate();
        let module = LLVMModuleCreateWithNameInContext(b"sum\0".as_ptr() as *const _, context);

        let void = LLVMVoidTypeInContext(context);
        let integer = LLVMInt64TypeInContext(context);

        let mut symbols: HashMap<String, Vec<Symbol>> = HashMap::new();

        let local_add_variable = |symbols: &mut HashMap<String, Vec<Symbol>>,
                                  builder: LLVMBuilderRef,
                                  n: String,
                                  t: Type,
                                  e: Option<Box<Expr>>| {
            let name = CString::new(n.clone()).unwrap();

            let decl = LLVMBuildAlloca(builder, integer, name.as_ptr() as *const _);
            if let Some(_) = e {
                LLVMBuildStore(builder, LLVMConstInt(integer, 0, 0), decl);
            }
            let new_symbol = Symbol::Variable(decl);
            symbols
                .entry(n.clone())
                .or_insert(Vec::new())
                .push(new_symbol);
        };

        let local_add_array = |symbols: &mut HashMap<String, Vec<Symbol>>,
                               builder: LLVMBuilderRef,
                               n: String,
                               t: Type,
                               s: u64,
                               e: Option<Vec<Box<Expr>>>| {
            let name = CString::new(n.clone()).unwrap();

            let array_type = LLVMArrayType(integer, s as u32);
            let decl = LLVMBuildArrayAlloca(
                builder,
                array_type,
                LLVMConstInt(integer, 0, 0),
                name.as_ptr() as *const _,
            );
            if let Some(e) = e {
                let mut args = e
                    .iter()
                    .map(|b| match **b {
                        Expr::Number(e) => LLVMConstInt(integer, e, 0),
                        _ => panic!("Cannot initialize global value with non-const expresion!"),
                    })
                    .collect::<Vec<_>>();
                let values = LLVMConstArray(array_type, args.as_mut_ptr(), args.len() as u32);
                LLVMBuildStore(builder, values, decl);
            }
            let new_symbol = Symbol::Array(s as u32, decl);
            symbols
                .entry(n.clone())
                .or_insert(Vec::new())
                .push(new_symbol);
        };

        let global_add_func = |symbols: &mut HashMap<String, Vec<Symbol>>,
                               n: String,
                               t: Option<Type>,
                               a: Option<Vec<FuncParam>>,
                               b: Block| {
            println!("Func");

            let builder = LLVMCreateBuilderInContext(context);
            let name = CString::new(n).unwrap();
            let t = if let Some(_) = t { void } else { integer };
            let mut args = if let Some(a) = a {
                a.iter().map(|_| integer).collect::<Vec<_>>()
            } else {
                Vec::new()
            };

            let function_type = LLVMFunctionType(t, args.as_mut_ptr(), args.len() as u32, 0);
            let function = LLVMAddFunction(module, name.as_ptr() as *const _, function_type);

            let basic_block =
                LLVMAppendBasicBlockInContext(context, function, b"entry\0".as_ptr() as *const _);
            LLVMPositionBuilderAtEnd(builder, basic_block);

            for i in b.decl {
                match i {
                    Decl::Single(n, t, e) => local_add_variable(symbols, builder, n, t, e),
                    Decl::Array(n, t, s, e) => local_add_array(symbols, builder, n, t, s, e),
                    _ => println!("uninplemented!"),
                }
            }

            let test = LLVMConstInt(integer, 0, 0);

            let sum = LLVMBuildAdd(builder, test, test, b"sum.0\0".as_ptr() as *const _);
            LLVMBuildRet(builder, sum);
            LLVMDisposeBuilder(builder);
        };

        let global_add_variable = |symbols: &mut HashMap<String, Vec<Symbol>>,
                                   n: String,
                                   t: Type,
                                   e: Option<Box<Expr>>| {
            println!("Single");
            let name = CString::new(n.clone()).unwrap();
            let decl = LLVMAddGlobal(module, integer, name.as_ptr() as *const _);
            if let Some(e) = e {
                let b = *e;
                if let Expr::Number(v) = b {
                    LLVMSetInitializer(decl, LLVMConstInt(integer, v as u64, 0));
                }
            } else {
                panic!("Cannot initialize global value with non-const expresion!");
            }
            let new_symbol = Symbol::Variable(decl);
            symbols
                .entry(n.clone())
                .or_insert(Vec::new())
                .push(new_symbol);
        };

        let global_add_array = |symbols: &mut HashMap<String, Vec<Symbol>>,
                                n: String,
                                t: Type,
                                s: u64,
                                e: Option<Vec<Box<Expr>>>| {
            println!("Array");
            let name = CString::new(n.clone()).unwrap();
            let array_type = LLVMArrayType(integer, s as u32);
            let decl = LLVMAddGlobal(module, array_type, name.as_ptr() as *const _);
            if let Some(e) = e {
                let mut args = e
                    .iter()
                    .map(|b| match **b {
                        Expr::Number(e) => LLVMConstInt(integer, e, 0),
                        _ => panic!("Cannot initialize global value with non-const expresion!"),
                    })
                    .collect::<Vec<_>>();
                let values = LLVMConstArray(array_type, args.as_mut_ptr(), args.len() as u32);
                LLVMSetInitializer(decl, values);
            }
            let new_symbol = Symbol::Array(s as u32, decl);
            symbols
                .entry(n.clone())
                .or_insert(Vec::new())
                .push(new_symbol);
        };

        for i in expr {
            match i {
                Decl::Single(n, t, e) => global_add_variable(&mut symbols, n, t, e),
                Decl::Array(n, t, s, e) => global_add_array(&mut symbols, n, t, s, e),
                Decl::Func(n, t, a, b) => global_add_func(&mut symbols, n, t, a, b),
            }
        }
        LLVMDumpModule(module);
        LLVMContextDispose(context);
    }
}
