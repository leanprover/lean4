/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.SimpUtil
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Sym.Simp.Main
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.Simp.Arith
import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Tactic.Grind.NormSymProcs
import Lean.Meta.Sym.Simp.Reduce
public import Lean.Meta.Sym.DSimp
import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.Util
import Lean.Meta.DiscrTree
public section
namespace Lean.Meta.Grind
open Sym.Simp (Simproc Discharger)

/-!
# `Sym.simp`-based `grind` normalizer

The `grind` normalizer runs on `Meta.simp` (see `simpCore`). This module is the `Sym.simp`
replacement, developed side by side with the legacy one: `normLegacy` and `normSym` apply the
respective simplification step to a term, and the `grind_norm` tactic exposes both so that
discrepancies can be collected as tests and fixed one by one.

`grind_norm` and the `normLegacy`/`normSym` pair are debugging aids for this migration only.
They will be deleted once `grind` runs on `Sym.simp`.

The `Sym.simp` theorem set is derived from the legacy `normExt` set on demand, so both
normalizers always see the same `[grind norm]` and `[grind unfold]` declarations.
-/

builtin_initialize registerTraceClass `grind.norm.sym

/-- The `grind` normalization theorems as `Sym.simp` theorem sets. -/
structure NormSymTheorems where
  /-- Theorems applied before visiting subterms (`[grind norm ↓]`). -/
  pre  : Sym.Simp.Theorems := {}
  /-- Theorems applied after visiting subterms (`[grind norm]`), and the equational theorems
  of the declarations to unfold (`[grind unfold]`). -/
  post : Sym.Simp.Theorems := {}
  /-- The `rfl`-theorems of `post` and the declarations to unfold, for `Sym.dsimp`. `grind` needs
  `dsimp` in one place: the right-hand side of a generalized pattern (`mkGeneralizedPatternEqProof`)
  must stay definitionally equal to the term it replaces, e.g. `Nat.succ x` becomes `x + 1`. -/
  dsimp : Sym.DSimp.Decls := {}

private def addNormSymTheorem (thms : Sym.Simp.Theorems) (thm : SimpTheorem) : MetaM Sym.Simp.Theorems := do
  -- Global simp theorems, including the reversed ones (`[grind norm ←]`), are stored as
  -- constants: `mkSimpTheoremFromConst` creates an auxiliary lemma when it has to adapt the
  -- statement.
  let .const declName _ := thm.proof
    | trace[grind.norm.sym] "skipping `{thm.origin.key}`, not a global declaration"
      return thms
  try
    return thms.insert (← Sym.Simp.mkTheoremFromDecl declName)
  catch ex =>
    trace[grind.norm.sym] "skipping `{.ofConstName declName}`: {ex.toMessageData}"
    return thms

/-- Builds the `Sym.simp` theorem sets from the legacy `grind` normalization theorem set. -/
def mkNormSymTheorems : MetaM NormSymTheorems := do
  let simpThms ← getNormTheorems
  let mut pre : Sym.Simp.Theorems := {}
  let mut post : Sym.Simp.Theorems := {}
  for thm in simpThms.pre.values do
    pre ← addNormSymTheorem pre thm
  -- The legacy `pushNot` simproc builds `b + 1 ≤ a` from `¬a ≤ b` by hand; here the theorems
  -- are rewrite rules, and `arith` normalizes the result.
  for declName in [``Nat.not_le_eq, ``Int.not_le_eq] do
    pre := pre.insert (← Sym.Simp.mkTheoremFromDecl declName)
  let mut dsimp : Sym.DSimp.Decls := {}
  for thm in simpThms.post.values do
    post ← addNormSymTheorem post thm
    if thm.rfl then
      if let .const declName _ := thm.proof then
        dsimp ← dsimp.add declName
  for declName in simpThms.toUnfold.toList do
    -- `Sym` preprocessing unfolds reducible declarations (e.g., `GE.ge`, `Ne`) eagerly.
    if (← isReducible declName) then continue
    try
      for thm in (← Sym.Simp.mkTheoremsFromDecl declName) do
        post := post.insert thm
      dsimp ← dsimp.add declName
    catch ex =>
      trace[grind.norm.sym] "skipping unfold `{.ofConstName declName}`: {ex.toMessageData}"
  return { pre, post, dsimp }

/-- `Sym.simp` methods approximating the legacy `grind` normalizer. -/
def mkNormSymMethods (config : Grind.Config) (thms : NormSymTheorems) : Sym.Simp.Methods := Id.run do
  let d : Discharger := Sym.Simp.dischargeSimpSelf
  let mut pre : Simproc := NormSym.eraseMData >> Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceControl
  if config.zeta then pre := pre >> Sym.Simp.zeta
  if config.zetaDelta then pre := pre >> Sym.Simp.zetaDeltaAll
  pre := pre >> NormSym.pushNot >> Sym.Simp.simpArith d (lhsOnly := true) >> thms.pre.rewrite d
  -- `grind` keeps bit-vector literals in `OfNat.ofNat` form.
  let post : Simproc := thms.post.rewrite d >> Sym.Simp.evalGround { bitVecOfNat := false } >> Sym.Simp.simpNatRel >> NormSym.simpEq >> NormSym.simpOr
    >> NormSym.simpDIte >> NormSym.reduceCtorEq >> NormSym.simpForall >> NormSym.simpExists
  return { pre, post }

/-- `Sym.dsimp` methods approximating the legacy `grind` `dsimp` step (`dsimpCore`). -/
def mkNormSymDSimpMethods (config : Grind.Config) (thms : NormSymTheorems) : Sym.DSimp.Methods := Id.run do
  let mut pre : Sym.DSimp.DSimproc := Sym.DSimp.beta >> Sym.DSimp.dsimpProj >> Sym.DSimp.dsimpMatch
  if config.zeta then pre := pre >> Sym.DSimp.zeta
  if config.zetaDelta then pre := pre >> Sym.DSimp.zetaDeltaAll
  let post : Sym.DSimp.DSimproc := thms.dsimp.toDSimproc >> Sym.DSimp.evalGround
  return { pre, post }

/--
Applies the legacy `simp`-based normalization step to `e`, and the metadata erasure that
`preprocess` performs after it. The `Sym.simp` chain erases metadata as part of the step.
-/
def normLegacy (e : Expr) : GrindM Simp.Result := do
  let r ← simpCore (← instantiateMVars e)
  return { r with expr := (← eraseIrrelevantMData r.expr) }

/-- Applies the `Sym.simp`-based normalization step to `e`. -/
def normSym (e : Expr) : GrindM Simp.Result := do
  let e ← Sym.preprocessExpr e
  let thms ← mkNormSymTheorems
  let methods := mkNormSymMethods (← getConfig) thms
  let (r, _) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) methods
  match r with
  | .rfl .. => return { expr := e }
  | .step e' h .. => return { expr := e', proof? := some h }

end Lean.Meta.Grind
