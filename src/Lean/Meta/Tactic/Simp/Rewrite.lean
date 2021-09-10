/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

def synthesizeArgs (lemmaName : Name) (xs : Array Expr) (bis : Array BinderInfo) (discharge? : Expr → SimpM (Option Expr)) : SimpM Bool := do
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      unless (← synthesizeInstance x type) do
        return false
    else if (← instantiateMVars x).isMVar then
      if (← isProp type) then
        match (← discharge? type) with
        | some proof =>
          unless (← isDefEq x proof) do
            trace[Meta.Tactic.simp.discharge] "{lemmaName}, failed to assign proof{indentExpr type}"
            return false
        | none =>
          trace[Meta.Tactic.simp.discharge] "{lemmaName}, failed to discharge hypotheses{indentExpr type}"
          return false
      else if (← isClass? type).isSome then
        unless (← synthesizeInstance x type) do
          return false
  return true
where
  synthesizeInstance (x type : Expr) : SimpM Bool := do
    match (← trySynthInstance type) with
    | LOption.some val =>
      if (← isDefEq x val) then
        return true
      else
        trace[Meta.Tactic.simp.discharge] "{lemmaName}, failed to assign instance{indentExpr type}"
        return false
    | _ =>
      trace[Meta.Tactic.simp.discharge] "{lemmaName}, failed to synthesize instance{indentExpr type}"
      return false

private def tryLemmaCore (lhs : Expr) (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (lemma : SimpLemma) (numExtraArgs : Nat) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Result) := do
  let rec go (e : Expr) : SimpM (Option Result) := do
    if (← isDefEq lhs e) then
      unless (← synthesizeArgs lemma.getName xs bis discharge?) do
        return none
      let proof ← instantiateMVars (mkAppN val xs)
      if ← hasAssignableMVar proof then
        trace[Meta.Tactic.simp.rewrite] "{lemma}, has unassigned metavariables after unification"
        return none
      let rhs   ← instantiateMVars type.appArg!
      if e == rhs then
        return none
      if lemma.perm && !Expr.lt rhs e then
        trace[Meta.Tactic.simp.rewrite] "{lemma}, perm rejected {e} ==> {rhs}"
        return none
      trace[Meta.Tactic.simp.rewrite] "{lemma}, {e} ==> {rhs}"
      return some { expr := rhs, proof? := proof }
    else
      unless lhs.isMVar do
        -- We do not report unification failures when `lhs` is a metavariable
        -- Example: `x = ()`
        -- TODO: reconsider if we want lemmas such as `(x : Unit) → x = ()`
        trace[Meta.Tactic.simp.unify] "{lemma}, failed to unify {lhs} with {e}"
      return none
  /- Check whether we need something more sophisticated here.
     This simple approach was good enough for Mathlib 3 -/
  let mut extraArgs := #[]
  let mut e := e
  for i in [:numExtraArgs] do
    extraArgs := extraArgs.push e.appArg!
    e := e.appFn!
  match (← go e) with
  | none => return none
  | some { expr := eNew, proof? := none } => return some { expr := mkAppN eNew extraArgs }
  | some { expr := eNew, proof? := some proof } =>
    let mut proof := proof
    for extraArg in extraArgs do
      proof ← mkCongrFun proof extraArg
    return some { expr := mkAppN eNew extraArgs, proof? := some proof }

def tryLemmaWithExtraArgs? (e : Expr) (lemma : SimpLemma) (numExtraArgs : Nat) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Result) :=
  withNewMCtxDepth do
    let val  ← lemma.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    tryLemmaCore lhs xs bis val type e lemma numExtraArgs discharge?

def tryLemma? (e : Expr) (lemma : SimpLemma) (discharge? : Expr → SimpM (Option Expr)) : SimpM (Option Result) := do
  withNewMCtxDepth do
    let val  ← lemma.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    match (← tryLemmaCore lhs xs bis val type e lemma 0 discharge?) with
    | some result => return some result
    | none =>
      let lhsNumArgs := lhs.getAppNumArgs
      let eNumArgs   := e.getAppNumArgs
      if eNumArgs > lhsNumArgs then
        tryLemmaCore lhs xs bis val type e lemma (eNumArgs - lhsNumArgs) discharge?
      else
        return none
/-
Remark: the parameter tag is used for creating trace messages. It is irrelevant otherwise.
-/
def rewrite (e : Expr) (s : DiscrTree SimpLemma) (erased : Std.PHashSet Name) (discharge? : Expr → SimpM (Option Expr)) (tag : String) : SimpM Result := do
  let candidates ← s.getMatchWithExtra e
  if candidates.isEmpty then
    trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
    return { expr := e }
  else
    let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.priority < e₂.1.priority
    for (lemma, numExtraArgs) in candidates do
      unless inErasedSet lemma do
        if let some result ← tryLemmaWithExtraArgs? e lemma numExtraArgs discharge? then
          return result
    return { expr := e }
where
  inErasedSet (lemma : SimpLemma) : Bool :=
    match lemma.name? with
    | none => false
    | some name => erased.contains name

def rewriteCtorEq? (e : Expr) : MetaM (Option Result) := withReducibleAndInstances do
  match e.eq? with
  | none => return none
  | some (_, lhs, rhs) =>
    let lhs ← whnf lhs
    let rhs ← whnf rhs
    let env ← getEnv
    match lhs.constructorApp? env, rhs.constructorApp? env with
    | some (c₁, _), some (c₂, _) =>
      if c₁.name != c₂.name then
        withLocalDeclD `h e fun h =>
          return some { expr := mkConst ``False, proof? := (← mkEqFalse' (← mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h))) }
      else
        return none
    | _, _ => return none

@[inline] def tryRewriteCtorEq (e : Expr) (x : SimpM Step) : SimpM Step := do
  match (← rewriteCtorEq? e) with
  | some r => return Step.done r
  | none => x

def rewriteUsingDecide? (e : Expr) : MetaM (Option Result) := withReducibleAndInstances do
  if e.hasFVar || e.hasMVar || e.isConstOf ``True || e.isConstOf ``False then
    return none
  else
    try
      let d ← mkDecide e
      let r ← withDefault <| whnf d
      if r.isConstOf ``true then
        return some { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
      else if r.isConstOf ``false then
        let h ← mkEqRefl d
        return some { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }
      else
        return none
    catch _ =>
      return none

@[inline] def tryRewriteUsingDecide (e : Expr) (x : SimpM Step) : SimpM Step := do
  if (← read).config.decide then
    match (← rewriteUsingDecide? e) with
    | some r => return Step.done r
    | none => x
  else
    x

def rewritePre (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  let lemmas ← (← read).simpLemmas
  return Step.visit (← rewrite e lemmas.pre lemmas.erased discharge? (tag := "pre"))

def rewritePost (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  let lemmas ← (← read).simpLemmas
  return Step.visit (← rewrite e lemmas.post lemmas.erased discharge? (tag := "post"))

def preDefault (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step :=
  tryRewriteCtorEq e <| rewritePre e discharge?

def postDefault (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  -- TODO: try equation lemmas
  tryRewriteCtorEq e <| tryRewriteUsingDecide e <| rewritePost e discharge?

end Lean.Meta.Simp
