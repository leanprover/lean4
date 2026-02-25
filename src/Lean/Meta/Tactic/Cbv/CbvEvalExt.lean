/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Data.NameMap
public import Lean.ScopedEnvExtension
public import Lean.Elab.InfoTree
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.AppBuilder

/-!
# `@[cbv_eval]` Attribute and Extension

Environment extension for user-provided `cbv` rewrite rules. Each theorem is converted
to a `Sym.Simp.Theorem` (precomputed `Pattern` + `DiscrTree` key) and indexed by the
head constant on its LHS.

`@[cbv_eval ←]` inverts the theorem: an auxiliary lemma with swapped sides is created
via `mkAuxLemma`.
-/

public section
namespace Lean.Meta.Sym.Simp

def Theorem.declName (thm : Theorem) : Option Name := thm.expr.getAppFn.constName?

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

/--
  Entry of the `CbvEvalExtension`.
  Consists of the precomputed `Theorem` object and a name of the head function appearing on the left-hand side of the theorem.
-/
structure CbvEvalEntry where
  appFn : Name
  thm  : Theorem
  deriving BEq, Inhabited

/-- Create a `CbvEvalEntry` from a theorem declaration. When `inv = true`, creates an
auxiliary lemma with swapped sides so the theorem can be used for right-to-left rewriting. -/
def mkCbvTheoremFromConst (declName : Name) (inv : Bool := false) : MetaM CbvEvalEntry := do
  let cinfo ← getConstVal declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  let type ← inferType val
  unless (← isProp type) do throwError "{val} is not a theorem and thus cannot be marked with `cbv_eval` attribute"
  let (fnName, thmDeclName) ← forallTelescope type fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "The conclusion {type} of theorem {val} is not an equality"
    let matchSide := if inv then rhs else lhs
    let some constName := matchSide.getAppFn.constName?
      | throwError "The rewrite side of theorem {val} is not an application of a constant"
    let mut thmDeclName := declName
    if inv then
      let invType ← mkForallFVars xs (← mkEq rhs lhs)
      let invVal ← mkLambdaFVars xs (← mkEqSymm (mkAppN val xs))
      thmDeclName ← mkAuxLemma (kind? := `_cbv_eval) cinfo.levelParams invType invVal
    return (constName, thmDeclName)
  let thm ← mkTheoremFromDecl thmDeclName
  return ⟨fnName, thm⟩

structure CbvEvalState where
  lemmas : NameMap Theorems := {}
  deriving Inhabited

def CbvEvalState.addEntry (s : CbvEvalState) (e : CbvEvalEntry) : CbvEvalState :=
  let existing := (s.lemmas.find? e.appFn).getD {}
  { s with lemmas := s.lemmas.insert e.appFn (existing.insert e.thm) }

abbrev CbvEvalExtension := SimpleScopedEnvExtension CbvEvalEntry CbvEvalState

builtin_initialize cbvEvalExt : CbvEvalExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvEvalExt
    initial  := {}
    addEntry := CbvEvalState.addEntry
    exportEntry? := fun level entry => do
      let theoremName ← entry.thm.declName
      guard (level == .private || !isPrivateName theoremName)
      return entry
  }

def getCbvEvalLemmas (target : Name) : CoreM (Option Theorems) := do
  let s := cbvEvalExt.getState (← getEnv)
  return (s.lemmas.find? target)

builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvEvalAttr
    name  := `cbv_eval
    descr := "Register a theorem as a rewrite rule for `cbv` evaluation of a given definition."
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun lemmaName stx kind => do
      let inv := !stx[1].isNone
      let (entry, _) ← MetaM.run (mkCbvTheoremFromConst lemmaName (inv := inv)) {}
      cbvEvalExt.add entry kind
  }

end Lean.Meta.Tactic.Cbv
