extern crate clap;
extern crate lalrpop_util;
extern crate llvm_sys as llvm;

#[macro_use]
mod ast;
mod gen;
mod grammar;

use clap::{app_from_crate, crate_authors, crate_description, crate_name, crate_version, Arg};
use std::env;
use std::fs;
use std::process::exit;

enum ExitCodes {
    Success = 0,
    FileError = 1,
    BadFormatParam = 2,
}

fn main() {
    let matches = app_from_crate!()
        .arg(
            Arg::with_name("input")
                .takes_value(true)
                .value_name("FILE")
                .help("File to compile"),
        )
        .get_matches();

    let input_file_name = match matches.value_of("i") {
        Some(f) => f,
        None => exit(ExitCodes::FileError as i32),
    };

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
            Err(err) => println!("{:?}", err),
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
