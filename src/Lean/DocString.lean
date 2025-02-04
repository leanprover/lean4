/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.DocString.Extension
import Lean.Parser.Tactic.Doc
import Lean.Parser.Term.Doc

set_option linter.missingDocs true

-- This module contains the main query interface for docstrings, which assembles user-visible
-- docstrings.
-- The module `Lean.DocString.Extension` contains the underlying data.

namespace Lean
open Lean.Parser.Tactic.Doc
open Lean.Parser.Term.Doc

/--
Finds the docstring for a name, taking tactic alternate forms and documentation extensions into
account.

Use `Lean.findSimpleDocString?` to look up the raw docstring without resolving alternate forms or
including extensions.
-/
def findDocString? (env : Environment) (declName : Name) (includeBuiltin := true) : IO (Option String) := do
  let declName := alternativeOfTactic env declName |>.getD declName
  let exts := getTacticExtensionString env declName
  let spellings := getRecommendedSpellingString env declName
  return (← findSimpleDocString? env declName (includeBuiltin := includeBuiltin)).map (· ++ exts ++ spellings)
