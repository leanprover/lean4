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
import Lean.Meta.Sym.Simp.Forall
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
-/

/-- The `grind` normalization theorems as `Sym.simp` theorem sets (`normSymExt`). -/
def getNormSymTheorems : CoreM NormSymTheorems :=
  return normSymExt.getState (← getEnv)

/-- `Sym.simp` methods approximating the legacy `grind` normalizer. -/
def mkNormSymMethods (config : Grind.Config) (thms : NormSymTheorems) : Sym.Simp.Methods := Id.run do
  let d : Discharger := Sym.Simp.dischargeSimpSelf
  let mut pre : Simproc := NormSym.eraseMData >> NormSym.preMatchCond >> NormSym.simpMatchDiscrsOnly
    >> Sym.Simp.beta >> NormSym.etaReduce >> Sym.Simp.reduceProj >> Sym.Simp.reduceControl >> Sym.Simp.simpExistsPropDomain
  if config.zeta then pre := pre >> Sym.Simp.zeta
  if config.zetaDelta then pre := pre >> Sym.Simp.zetaDeltaAll
  pre := pre >> NormSym.pushNot >> Sym.Simp.simpArith d (lhsOnly := true) (distrib := config.distrib) (maxChar? := some config.maxChar) >> thms.pre.rewrite d
  -- `grind` keeps bit-vector literals in `OfNat.ofNat` form.
  let post : Simproc := thms.post.rewrite d >> Sym.Simp.evalGround { bitVecOfNat := false } >> Sym.Simp.simpNatRel
    >> Sym.Simp.simpNatSub (distrib := config.distrib) >> NormSym.simpEq >> NormSym.simpOr
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

/-- Applies the `Sym.simp`-based normalization step (`symNorm`) to `e`. -/
def normSym (e : Expr) : GrindM Simp.Result := do
  let thms ← getNormSymTheorems
  let config ← getConfig
  let (r, _, _) ← symNorm e (mkNormSymMethods config thms) (mkNormSymDSimpMethods config thms) {} {}
  return r

end Lean.Meta.Grind
