" Vim syntax file
" Language: Nanilang
" Maintainer: Guilherme Chichanoski

if exists("b:current_syntax")
    finish
endif

syn keyword reservedWords let def if else while for
syn keyword commands read write stop skip return
syn keyword types int bool string
syn keyword boolean true false

syn match number '\d\+'
syn match number '[+-]\d\+'
syn match string '"\.\*"'
syn match identifier '[a-zA-Z]\+'

syn region block start="{" end="}" fold transparent

let b:current_syntax = "nani"

hi def link number   Constant
hi def link boolean  Constant
hi def link types    Type
hi def link commands Statement
hi def link reservedWords Special
hi def link identifier Directory
hi def link function SpecialKey
