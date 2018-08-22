/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Term-level readers and macros
-/
prelude
import init.lean.parser.reader.token

namespace lean.parser
namespace reader
open combinators

def hole := {macro . name := `hole}

def hole.reader : reader :=
node hole [symbol "_"]

@[derive reader.has_view]
def term.reader :=
any_of [
  hole.reader
]

end reader
end lean.parser
