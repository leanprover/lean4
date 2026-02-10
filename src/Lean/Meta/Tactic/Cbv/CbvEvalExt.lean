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

def mkCbvTheoremFromConst (declName : Name) : MetaM CbvEvalEntry := do
  let cinfo ← getConstVal declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  let type ← inferType val
  unless (← isProp type) do throwError "{val} is not a theorem and thus cannot be marked with `cbv_eval` attribute"
  let fnName ← forallTelescope type fun _ body => do
    let some (_, lhs, _) := body.eq? | throwError "The conclusion {type} of theorem {val} is not an equality"
    let appFn := lhs.getAppFn
    let some constName := appFn.constName? | throwError "The left-hand side of a theorem {val} is not an application of a constant"
    return constName
  let thm ← mkTheoremFromDecl declName
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
    add := fun lemmaName _ kind => do
      let (entry, _) ← MetaM.run (mkCbvTheoremFromConst lemmaName) {}
      cbvEvalExt.add entry kind
  }

end Lean.Meta.Tactic.Cbv
