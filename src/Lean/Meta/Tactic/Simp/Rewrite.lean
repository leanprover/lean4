/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

/-
Remark: the parameter tag is used for creating trace messages. It is irrelevant otherwise.
-/
def rewrite (e : Expr) (s : DiscrTree SimpLemma) (discharge? : Expr → SimpM σ (Option Expr)) (tag : String) : SimpM σ Result := do
  let lemmas ← s.getMatch e
  if lemmas.isEmpty then
    trace[Meta.Tactic.simp]! "no lemmas found for {tag}-rewriting {e}"
    return { expr := e }
  else
    let lemmas := lemmas.insertionSort fun e₁ e₂ => e₁.priority < e₂.priority
    for lemma in lemmas do
      if let some result ← tryLemma? lemma then
        return result
    return { expr := e }
where
  getLHS (kind : SimpLemmaKind) (type : Expr) : MetaM Expr :=
    match kind with
    | SimpLemmaKind.pos => return type
    | SimpLemmaKind.neg => return type.appArg!
    | SimpLemmaKind.eq  => return type.appFn!.appArg!
    | SimpLemmaKind.iff => return type.appFn!.appArg!

  getRHS (kind : SimpLemmaKind) (type : Expr) : MetaM Expr :=
    match kind with
    | SimpLemmaKind.pos => return mkConst `True
    | SimpLemmaKind.neg => return mkConst `False
    | SimpLemmaKind.eq  => return type.appArg!
    | SimpLemmaKind.iff => return type.appArg!

  synthesizeArgs (lemma : SimpLemma) (xs : Array Expr) (bis : Array BinderInfo) : SimpM σ Bool := do
    for x in xs, bi in bis do
      let type ← inferType x
      if bi.isInstImplicit then
        match ← trySynthInstance type with
        | LOption.some val =>
          unless (← isDefEq x val) do
            trace[Meta.Tactic.simp.discharge]! "{lemma}, failed to assign instance{indentExpr type}"
            return false
        | _ =>
          trace[Meta.Tactic.simp.discharge]! "{lemma}, failed to synthesize instance{indentExpr type}"
          return false
      else if (← isProp type <&&> (← instantiateMVars x).isMVar) then
        match ← discharge? type with
        | some proof =>
          unless (← isDefEq x proof) do
            trace[Meta.Tactic.simp.discharge]! "{lemma}, failed to assign proof{indentExpr type}"
            return false
        | none =>
          trace[Meta.Tactic.simp.discharge]! "{lemma}, failed to discharge hypotheses{indentExpr type}"
          return false
    return true

  finalizeProof (kind : SimpLemmaKind) (proof : Expr) : MetaM Expr :=
    match kind with
    | SimpLemmaKind.eq  => return proof
    | SimpLemmaKind.iff => mkPropExt proof
    | SimpLemmaKind.pos => mkEqTrue proof
    | SimpLemmaKind.neg => mkEqFalse proof

  tryLemma? (lemma : SimpLemma) : SimpM σ (Option Result) :=
    withNewMCtxDepth do
      let val  ← lemma.getValue
      let type ← inferType val
      let (xs, bis, type) ← forallMetaTelescopeReducing type
      let lhs ← getLHS lemma.kind type
      if (← isDefEq lhs e) then
        unless (← synthesizeArgs lemma xs bis) do
          return none
        let proof ← instantiateMVars (mkAppN val xs)
        if ← hasAssignableMVar proof then
          return none
        let rhs   ← instantiateMVars (← getRHS lemma.kind type)
        if lemma.perm && !Expr.lt rhs e then
          trace[Meta.Tactic.simp.unify]! "{lemma}, perm rejected {e} ==> {rhs}"
          return none
        let proof ← finalizeProof lemma.kind proof
        trace[Meta.Tactic.simp.rewrite]! "{lemma}, {e} ==> {rhs}"
        return some { expr := rhs, proof? := proof }
      else
        trace[Meta.Tactic.simp.unify]! "{lemma}, failed to unify {lhs} with {e}"
        return none

def preDefault (e : Expr) (discharge? : Expr → SimpM σ (Option Expr)) : SimpM σ Step := do
  let lemmas ← (← read).simpLemmas
  return Step.visit (← rewrite e lemmas.pre discharge? (tag := "pre"))

def postDefault (e : Expr) (discharge? : Expr → SimpM σ (Option Expr)) : SimpM σ Step := do
  let lemmas ← (← read).simpLemmas
  return Step.visit (← rewrite e lemmas.post discharge? (tag := "post"))

end Lean.Meta.Simp
