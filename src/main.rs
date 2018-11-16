extern crate clap;
extern crate codespan;
extern crate codespan_reporting;
extern crate lalrpop_util;
extern crate llvm_sys as llvm;

#[macro_use]
mod ast;
mod gen;
mod grammar;
mod symbol_table;

use clap::{app_from_crate, crate_authors, crate_description, crate_name, crate_version, Arg};
use lalrpop_util::ParseError;
use codespan::{ByteIndex, CodeMap, Span};
use codespan_reporting::termcolor::{ColorChoice, StandardStream};
use codespan_reporting::{emit, Diagnostic, Label};
use std::process::exit;

enum ExitCodes {
    FileError = 1,
}

fn main() {
    let matches = app_from_crate!()
        .arg(
            Arg::with_name("input")
                .takes_value(true)
                .value_name("FILE")
                .required(true)
                .help("File to compile"),
        )
        .get_matches();

    let input_file_name = matches.value_of("input").unwrap();

    let mut code_map = CodeMap::new();
    let writer = StandardStream::stderr(ColorChoice::Always);

    let file = match code_map.add_filemap_from_disk(input_file_name) {
        Ok(file) => file,
        Err(_) => {
            let file_error_diagnose =
                Diagnostic::new_error(format!("no such file: {}", input_file_name));
            emit(writer, &code_map, &file_error_diagnose).unwrap();
            exit(ExitCodes::FileError as i32)
        }
    };

    unsafe {
        let mut erros = vec![];
        match grammar::ProgramParser::new().parse(&mut erros, &file.src()) {
            Ok(expr) => gen::gen(expr),
            Err(err) => match err {
                ParseError::UnrecognizedToken { token, expected } => {
                    let (start, token, end) = match token {
                        Some((start, token, end)) => (
                            ByteIndex::from((start + 1) as u32),
                            token.1,
                            ByteIndex::from((end + 1) as u32),
                        ),
                        None => (ByteIndex::none(), "EOF", ByteIndex::none()),
                    };

                    let diagnostic = Diagnostic::new_error(format!(
                        "{} found, but expect {:?}",
                        token, expected
                    ));

                    let span = Span::new(start, end);

                    let label = Label::new_primary(span);
                    emit(writer, &code_map, &diagnostic.with_label(label)).unwrap();
                }
                ParseError::User { error } => {
                    let diagnostic = Diagnostic::new_error(error);

                    emit(writer, &code_map, &diagnostic).unwrap();
                }
                ParseError::ExtraToken { token } => {
                    let (start, token, end) = (
                        ByteIndex::from((token.0 + 1) as u32),
                        token.1,
                        ByteIndex::from((token.2 + 1) as u32),
                    );

                    let diagnostic =
                        Diagnostic::new_error(format!("{} found, but was not expected", token));

                    let span = Span::new(start, end);

                    let label = Label::new_primary(span);
                    emit(writer, &code_map, &diagnostic.with_label(label)).unwrap();
                }
                ParseError::InvalidToken { location } => {
                    let span = file
                        .line_span(
                            file.find_line(ByteIndex::from((location + 1) as u32))
                                .unwrap(),
                        )
                        .unwrap();

                    let diagnostic = Diagnostic::new_error("invalid line or EOF");
                    let label = Label::new_primary(span);

                    emit(writer, &code_map, &diagnostic.with_label(label)).unwrap();
                }
            },
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
