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
open monad_parser

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

def module := {macro . name := `module}

def module.reader : reader :=
node module [
  optional prelude.reader,
  many import.reader
]

end reader
end lean.parser
