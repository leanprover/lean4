/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Util.CollectMVars
import Lean.Meta.Basic

namespace Lean.Meta

/--
  Data for user-defined theorems marked with the `congr` attribute.

  This type should be confused with `CongrTheorem` which represents different kinds of automatically
  generated congruence theorems. The `simp` tactic also uses some of them.
-/
structure SimpCongrTheorem where
  theoremName   : Name
  funName       : Name
  hypothesesPos : Array Nat
  priority      : Nat
deriving Inhabited, Repr

structure SimpCongrTheorems where
  lemmas : SMap Name (List SimpCongrTheorem) := {}
  deriving Inhabited, Repr

def SimpCongrTheorems.get (d : SimpCongrTheorems) (declName : Name) : List SimpCongrTheorem :=
  match d.lemmas.find? declName with
  | none    => []
  | some cs => cs

def addSimpCongrTheoremEntry (d : SimpCongrTheorems) (e : SimpCongrTheorem) : SimpCongrTheorems :=
  { d with lemmas :=
      match d.lemmas.find? e.funName with
      | none    => d.lemmas.insert e.funName [e]
      | some es => d.lemmas.insert e.funName <| insert es }
where
  insert : List SimpCongrTheorem → List SimpCongrTheorem
    | []     => [e]
    | e'::es => if e.priority ≥ e'.priority then e::e'::es else e' :: insert es

builtin_initialize congrExtension : SimpleScopedEnvExtension SimpCongrTheorem SimpCongrTheorems ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := addSimpCongrTheoremEntry
    finalizeImport := fun s => { s with lemmas := s.lemmas.switch }
  }

def mkSimpCongrTheorem (declName : Name) (prio : Nat) : MetaM SimpCongrTheorem := withReducible do
  let c ← mkConstWithLevelParams declName
  let (xs, bis, type) ← forallMetaTelescopeReducing (← inferType c)
  match type.eqOrIff? with
  | none => throwError "invalid 'congr' theorem, equality expected{indentExpr type}"
  | some (lhs, rhs) =>
    lhs.withApp fun lhsFn lhsArgs => rhs.withApp fun rhsFn rhsArgs => do
      unless lhsFn.isConst && rhsFn.isConst && lhsFn.constName! == rhsFn.constName! && lhsArgs.size == rhsArgs.size do
        throwError "invalid 'congr' theorem, equality left/right-hand sides must be applications of the same function{indentExpr type}"
      let mut foundMVars : MVarIdSet := {}
      for lhsArg in lhsArgs do
        for mvarId in (lhsArg.collectMVars {}).result do
          foundMVars := foundMVars.insert mvarId
      let mut i := 0
      let mut hypothesesPos := #[]
      for x in xs, bi in bis do
        if bi.isExplicit && !foundMVars.contains x.mvarId! then
          let rhsFn? ← forallTelescopeReducing (← inferType x) fun ys xType => do
            match xType.eqOrIff? with
            | none => pure none -- skip
            | some (xLhs, xRhs) =>
              let mut j := 0
              for y in ys do
                let yType ← inferType y
                unless onlyMVarsAt yType foundMVars do
                  throwError "invalid 'congr' theorem, argument #{j+1} of parameter #{i+1} contains unresolved parameter{indentExpr yType}"
                j := j + 1
              unless onlyMVarsAt xLhs foundMVars do
                throwError "invalid 'congr' theorem, parameter #{i+1} is not a valid hypothesis, the left-hand-side contains unresolved parameters{indentExpr xLhs}"
              let xRhsFn := xRhs.getAppFn
              unless xRhsFn.isMVar do
                throwError "invalid 'congr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side head is not a metavariable{indentExpr xRhs}"
              unless !foundMVars.contains xRhsFn.mvarId! do
                throwError "invalid 'congr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side head was already resolved{indentExpr xRhs}"
              for arg in xRhs.getAppArgs do
                unless arg.isFVar do
                  throwError "invalid 'congr' theorem, parameter #{i+1} is not a valid hypothesis, the right-hand-side argument is not local variable{indentExpr xRhs}"
              pure (some xRhsFn)
          match rhsFn? with
          | none       => pure ()
          | some rhsFn =>
            foundMVars    := foundMVars.insert x.mvarId! |>.insert rhsFn.mvarId!
            hypothesesPos := hypothesesPos.push i
        i := i + 1
      return {
        theoremName   := declName
        funName       := lhsFn.constName!
        hypothesesPos := hypothesesPos
        priority      := prio
      }
where
  /-- Return `true` if `t` contains a metavariable that is not in `mvarSet` -/
  onlyMVarsAt (t : Expr) (mvarSet : MVarIdSet) : Bool :=
    Option.isNone <| t.find? fun e => e.isMVar && !mvarSet.contains e.mvarId!

def addSimpCongrTheorem (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let lemma ← mkSimpCongrTheorem declName prio
  congrExtension.add lemma attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `congr
    descr := "congruence theorem"
    add   := fun declName stx attrKind => do
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addSimpCongrTheorem declName attrKind prio |>.run {} {}
  }

def getSimpCongrTheorems : MetaM SimpCongrTheorems :=
  return congrExtension.getState (← getEnv)

end Lean.Meta
