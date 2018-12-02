use super::super::ast::Type;
use std::collections::{HashMap, LinkedList};

use llvm::prelude::*;

// TODO Should store the type
#[derive(Clone, Debug)]
pub enum Symbol {
    Variable(LLVMValueRef, Type),
    Array(LLVMValueRef, Type),
    Func(LLVMValueRef, (Type, Vec<Type>)), // TODO Should store tha function value and signature
}

#[derive(Clone, Debug)]
pub struct SymbolTable {
    list: LinkedList<HashMap<String, Symbol>>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        let mut linked = LinkedList::new();
        linked.push_front(HashMap::new());
        SymbolTable { list: linked }
    }

    /// Get the symbol `identifier` in the current scope or in a lower scope
    pub fn get(self: &Self, identifier: &str) -> Result<&Symbol, ()> {
        for hash_symbol in self.list.iter() {
            if let Some(symbol) = hash_symbol.get(identifier) {
                return Ok(symbol);
            }
        }

        Err(())
    }

    /// Should be call on a new ssope creation
    pub fn initialize_scope(self: &mut Self) {
        self.list.push_front(HashMap::new());
    }

    /// To be used when the scope ended
    pub fn kill_scope(self: &mut Self) {
        self.list.pop_front();
    }

    /// This function only set a identifier in the scope, possibly it will
    /// overwrite the value thats is current in the actual scope
    pub fn set(
        self: &mut Self,
        identifier: &str,
        symbol: Symbol,
    ) -> Result<(), ()> {
        let front = self.list.front_mut().unwrap();
        if front.get(identifier).is_some() {
            Err(())
        } else {
            front.insert(identifier.to_string(), symbol);
            Ok(())
        }
    }
}
