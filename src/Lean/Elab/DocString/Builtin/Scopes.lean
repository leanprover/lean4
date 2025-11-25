/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude

public import Lean.Elab.DocString
import Lean.Elab.DocString.Builtin.Parsing

namespace Lean.Doc
open Lean.Parser

public section

inductive DocScope where
  | local
  | import (mods : Array Name)

private def imports := leading_parser sepBy1 ident ", "

instance : FromDocArg DocScope where
  fromDocArg v := private
    match v with
    | .str s => do
      let stx ← withRef s <| parseQuotedStrLit (whitespace >> imports.fn) s
      let `(imports|$modNames,*) := stx
        | throwErrorAt stx "Expected comma-separated imports list, got `{stx}`"
      let modNames : Array Ident := modNames
      return .import (modNames.map (·.getId))
    | .ident x =>
      let y := x.getId.eraseMacroScopes
      if y == `local then pure .local
      else throwErrorAt x "Unexpected identifier, expected `local` or a string of imports"
    | .num n => throwErrorAt n "Unexpected number `{n}`"
