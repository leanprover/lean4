/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.SimpUtil
public import Lean.Meta.Tactic.Grind.NormSym
import Lean.Meta.Sym.Simp.Main
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Simp.Main
public section
namespace Lean.Meta.Grind

/-!
Entry point of the `grind` normalizer at attribute time, selecting the legacy `simp`-based
normalizer or the `Sym.simp`-based one by `backward.grind.normalizer`. The `GrindM` entry points
(`simpCore`, `dsimpCore`) dispatch in `Lean.Meta.Tactic.Grind.Simp`.
-/

set_option compiler.ignoreBorrowAnnotation true in
/-- Normalizes `e` at attribute time (E-matching patterns). -/
@[export lean_grind_normalize]
def normalizeImp (e : Expr) (config : Grind.Config) : MetaM Expr := do
  if backward.grind.normalizer.get (← getOptions) then
    let (r, _) ← Meta.simp e (← Grind.getSimpContext config) (← Grind.getSimprocs)
    return r.expr
  else Sym.SymM.run do
    let e ← Sym.preprocessExpr e
    let methods := mkNormSymMethods config (← mkNormSymTheorems)
    let (r, _) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) methods
    match r with
    | .rfl .. => return e
    | .step e' .. => return e'

end Lean.Meta.Grind
