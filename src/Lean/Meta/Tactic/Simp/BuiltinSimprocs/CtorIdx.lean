/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Simproc
import Init.Simproc
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.CtorRecognizer
open Lean Meta Simp
public section

/--
This simproc reduces `T.ctorIdx (T.con …)` to the constructor index.
It does not take part in simp's discrimination tree index, so can be costly on large goals.
-/
builtin_dsimproc_decl reduceCtorIdx (_) := fun e => e.withApp fun f xs => do
  let some fnName := f.constName? | return .continue
  let some indInfo ← isCtorIdx? fnName | return .continue
  unless xs.size == indInfo.numParams + indInfo.numIndices + 1 do return .continue
  let some conInfo ← isConstructorApp? xs.back! | return .continue
  let e' := mkNatLit conInfo.cidx
  return .done e'

end
