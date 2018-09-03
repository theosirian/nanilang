extern crate getopts;
extern crate lalrpop_util;
extern crate llvm_sys as llvm;

mod ast;
mod gen;
mod grammar;

use getopts::Options;

use std::env;
use std::fs;
use std::process::exit;

enum ExitCodes {
    Success = 0,
    FileError = 1,
    BadFormatParam = 2,
}

fn print_usage(opt: Options) {
    println!("{}", opt.usage(&"Compile the nani lang"));
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "help option")
        .optopt("i", "input", "input file", "FILE");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(_) => {
            print_usage(opts);
            exit(ExitCodes::BadFormatParam as i32);
        }
    };

    let input_file_name = match matches.opt_str("i") {
        Some(f) => f,
        None => match matches.free.len() {
            1 => matches.free[0].clone(),
            _ => {
                print_usage(opts);
                exit(ExitCodes::FileError as i32);
            }
        },
    };

    if matches.opt_present("h") {
        print_usage(opts);
        exit(ExitCodes::Success as i32);
    }

    let content = match fs::read_to_string(input_file_name) {
        Ok(c) => c,
        Err(e) => {
            println!("Error on file read: {}", e);
            exit(ExitCodes::FileError as i32);
        }
    };

    unsafe {
        let mut erros = vec![];
        match grammar::ProgramParser::new().parse(&mut erros, &content) {
            Ok(expr) => gen::gen(expr),
            Err(err) => {}
        }
    }
}

#[test]
fn parse_var_decl_with_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let a = 2 : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [ast::Decl::Single(
            "a".to_string(),
            ast::Type::Int,
            Some(Box::new(ast::Expr::Number(2)))
        )]
    );
}

#[test]
fn parse_var_decl_without_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let a : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [ast::Decl::Single("a".to_string(), ast::Type::Int, None)]
    );
}

#[test]
fn parse_var_multi_decl_without_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let a, b,c : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [
            ast::Decl::Single("a".to_string(), ast::Type::Int, None),
            ast::Decl::Single("b".to_string(), ast::Type::Int, None),
            ast::Decl::Single("c".to_string(), ast::Type::Int, None)
        ]
    );
}

#[test]
fn parse_var_multi_decl_with_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let a = 1, b  =2,c = 3 : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [
            ast::Decl::Single(
                "a".to_string(),
                ast::Type::Int,
                Some(Box::new(ast::Expr::Number(1)))
            ),
            ast::Decl::Single(
                "b".to_string(),
                ast::Type::Int,
                Some(Box::new(ast::Expr::Number(2)))
            ),
            ast::Decl::Single(
                "c".to_string(),
                ast::Type::Int,
                Some(Box::new(ast::Expr::Number(3)))
            )
        ]
    );
}

#[test]
fn parse_var_decl_with_expr_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let a = b + 1 : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [ast::Decl::Single(
            "a".to_string(),
            ast::Type::Int,
            Some(Box::new(ast::Expr::Op(
                Box::new(ast::Expr::Variable(ast::Variable::Single("b".to_string()))),
                ast::Opcode::Add,
                Box::new(ast::Expr::Number(1))
            )))
        )]
    );
}

#[test]
fn parse_var_decl_array_int_without_init() {
    let mut errors = vec![];

    let var_decl = grammar::ProgramParser::new()
        .parse(&mut errors, "let v[10] : int;")
        .unwrap();

    assert_eq!(
        var_decl,
        [ast::Decl::Array("v".to_string(), ast::Type::Int, 10, None)]
    );
}
