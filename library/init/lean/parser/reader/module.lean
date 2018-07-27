/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level readers and macros
-/
prelude
import init.lean.parser.reader.token init.lean.parser.reader.term

namespace lean.parser
namespace reader
open combinators

def symbol_coe : has_coe string reader := ⟨symbol⟩
def seq_coe : has_coe_t (list reader) reader := ⟨seq⟩
local attribute [instance] symbol_coe seq_coe

-- coerce all list literals to `list reader`
local notation `[` l:(foldr `, ` (h t, @list.cons reader h t) list.nil `]`) := l

local postfix `?`:10000 := optional
local postfix *:10000 := many
local postfix +:10000 := many1

def «prelude» := {macro . name := `prelude}

def prelude.reader : reader :=
node «prelude» ["prelude"]

def import_path := {macro . name := `import_path}

def import_path.reader : reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node import_path [(raw_symbol ".")*, ident]

def «import» := {macro . name := `import}

def import.reader : reader :=
node «import» ["import", import_path.reader+]

section commands

def «open» := {macro . name := `open}

def open_export.reader : reader :=
[ident,
 ["as", ident]?,
 [try ["(", ident], ident*, ")"]?,
 [try ["(", "renaming"], [ident, "->", ident]+, ")"]?,
 ["(", "hiding", ident+, ")"]?
]+

def open.reader : reader :=
node «open» ["open", open_export.reader]

def «section» := {macro . name := `section}

def section.reader : reader :=
node «section» ["section", ident?, recurse*, "end", ident?]

def «notation» := {macro . name := `notation}

def prec : reader := [":", number]/-TODO <|> expr-/

def quoted_symbol : read_m syntax :=
do (s, info) ← with_source_info $ monad_parsec.take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

def notation_tk :=
any_of [
  [raw_symbol "`", {read := quoted_symbol}, raw_symbol "`", prec?]
  --TODO, {read := do tk ← token, /- check if reserved token-/}
]

def action : reader :=
[":", any_of [
  number,
  "max",
  "prev",
  "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/]]

def notation_reader : reader :=
any_of [
  number,
  [ident?,
   [notation_tk,
    (any_of [
      ["binder", prec?],
      ["binders", prec?],
      [ident, action?]
    ])?
   ]*
  ]
]

def notation.reader : reader :=
node «notation» ["notation", notation_reader, ":=", term.reader]

def command.reader :=
with_recurse $ any_of [open.reader, section.reader, notation.reader] <?> "command"
end commands

def module := {macro . name := `module}

def module.reader : reader :=
node module [prelude.reader?, import.reader*, command.reader*]

end reader
end lean.parser
