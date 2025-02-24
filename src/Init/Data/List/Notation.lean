/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Div.Basic

/-!
# Notation for `List` literals.
-/

set_option linter.missingDocs true -- keep it documented
-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Decidable List

/--
The syntax `[a, b, c]` is shorthand for `a :: b :: c :: []`, or
`List.cons a (List.cons b (List.cons c List.nil))`. It allows conveniently constructing
list literals.

For lists of length at least 64, an alternative desugaring strategy is used
which uses let bindings as intermediates as in
`let left := [d, e, f]; a :: b :: c :: left` to avoid creating very deep expressions.
Note that this changes the order of evaluation, although it should not be observable
unless you use side effecting operations like `dbg_trace`.
-/
syntax "[" withoutPosition(term,*,?) "]"  : term

recommended_spelling "nil" for "[]" in [List.nil, «term[_]»]
recommended_spelling "singleton" for "[a]" in [List.cons, «term[_]»]

/--
Auxiliary syntax for implementing `[$elem,*]` list literal syntax.
The syntax `%[a,b,c|tail]` constructs a value equivalent to `a::b::c::tail`.
It uses binary partitioning to construct a tree of intermediate let bindings as in
`let left := [d, e, f]; a :: b :: c :: left` to avoid creating very deep expressions.
-/
syntax "%[" withoutPosition(term,*,? " | " term) "]" : term

namespace Lean

macro_rules
  | `([ $elems,* ]) => do
    -- NOTE: we do not have `TSepArray.getElems` yet at this point
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(List.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expandListLit size (size % 2 == 0) (← ``(List.nil))
    else
      `(%[ $elems,* | List.nil ])

end Lean
