/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Module-level readers and macros
-/
prelude
import init.lean.parser.reader.token

namespace lean.parser
namespace reader
open combinators

def «prelude» := {macro . name := `prelude}

def prelude.reader : reader :=
node «prelude» [keyword "prelude"]

def import_path := {macro . name := `import_path}

def import_path.reader : reader :=
-- use `raw_symbol` to ignore registered tokens like ".."
node import_path [many (raw_symbol "."), ident]

def «import» := {macro . name := `import}

def import.reader : reader :=
node «import» [keyword "import", many1 import_path.reader]

section commands

def «open» := {macro . name := `open}

def open_export.reader : reader :=
many1 $ seq [
  ident,
  optional $ seq [
    keyword "as",
    ident
  ],
  optional $ seq [
    try $ seq [symbol "(", ident],
    many ident,
    symbol ")"
  ],
  optional $ seq [
    try $ seq [symbol "(", keyword "renaming"],
    many1 $ seq [ident, symbol "->", ident],
    symbol ")"
  ],
  optional $ seq [
    symbol "(",
    keyword "hiding",
    many1 ident,
    symbol ")"
  ]
]

def open.reader : reader :=
node «open» [keyword "open", open_export.reader]

def «section» := {macro . name := `section}

def section.reader : reader :=
node «section» [
  keyword "section",
  optional ident,
  many recurse,
  keyword "end",
  optional ident]

def command.reader :=
with_recurse $ any_of [open.reader, section.reader] <?> "command"
end commands

def module := {macro . name := `module}

def module.reader : reader :=
node module [
  optional prelude.reader,
  many import.reader,
  many command.reader
]

end reader
end lean.parser
