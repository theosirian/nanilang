use std::collections::{HashMap, LinkedList};

use llvm::prelude::*;

#[derive(Clone, Debug)]
pub enum Symbol {
    Variable(LLVMValueRef),
    Array(u32, LLVMValueRef),
    ArrayRef(LLVMValueRef),
    Func(String),
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
    pub fn set(self: &mut Self, identifier: &str, symbol: Symbol) {
        let front = self.list.front_mut().unwrap();
        front.insert(identifier.to_string(), symbol);
    }
}
