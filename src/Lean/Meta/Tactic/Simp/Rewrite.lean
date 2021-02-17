/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

def synthesizeArgs (lemmaName : Name) (xs : Array Expr) (bis : Array BinderInfo) (discharge? : Expr → SimpM (Option Expr)) : SimpM Bool := do
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      match ← trySynthInstance type with
      | LOption.some val =>
        unless (← isDefEq x val) do
          trace[Meta.Tactic.simp.discharge]! "{lemmaName}, failed to assign instance{indentExpr type}"
          return false
      | _ =>
        trace[Meta.Tactic.simp.discharge]! "{lemmaName}, failed to synthesize instance{indentExpr type}"
        return false
    else if (← isProp type <&&> (← instantiateMVars x).isMVar) then
      match ← discharge? type with
      | some proof =>
        unless (← isDefEq x proof) do
          trace[Meta.Tactic.simp.discharge]! "{lemmaName}, failed to assign proof{indentExpr type}"
          return false
      | none =>
        trace[Meta.Tactic.simp.discharge]! "{lemmaName}, failed to discharge hypotheses{indentExpr type}"
        return false
  return true

/-
Remark: the parameter tag is used for creating trace messages. It is irrelevant otherwise.
-/
def rewrite (e : Expr) (s : DiscrTree SimpLemma) (discharge? : Expr → SimpM (Option Expr)) (tag : String) : SimpM Result := do
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
    | SimpLemmaKind.ne  => mkEq type.appFn!.appArg! type.appArg!

  getRHS (kind : SimpLemmaKind) (type : Expr) : MetaM Expr :=
    match kind with
    | SimpLemmaKind.pos => return mkConst `True
    | SimpLemmaKind.neg => return mkConst `False
    | SimpLemmaKind.eq  => return type.appArg!
    | SimpLemmaKind.iff => return type.appArg!
    | SimpLemmaKind.ne  => return mkConst `False

  finalizeProof (kind : SimpLemmaKind) (proof : Expr) : MetaM Expr :=
    match kind with
    | SimpLemmaKind.eq  => return proof
    | SimpLemmaKind.iff => mkPropExt proof
    | SimpLemmaKind.pos => mkEqTrue proof
    | SimpLemmaKind.neg => mkEqFalse proof
    | SimpLemmaKind.ne  => mkEqFalse proof

  tryLemma? (lemma : SimpLemma) : SimpM (Option Result) :=
    withNewMCtxDepth do
      let val  ← lemma.getValue
      let type ← inferType val
      let (xs, bis, type) ← forallMetaTelescopeReducing type
      let type ← instantiateMVars type
      let lhs ← getLHS lemma.kind type
      if (← isDefEq lhs e) then
        unless (← synthesizeArgs lemma.getName xs bis discharge?) do
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
  if e.hasFVar || e.hasMVar then
    return none
  else
    try
      let d ← mkDecide e
      let r ← withDefault <| whnf d
      if r.isConstOf ``true then
        return some { expr := mkConst ``True, proof? := mkAppN (mkConst ``eqTrueOfDecide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
      else if r.isConstOf ``false then
        let h ← mkEqRefl d
        return some { expr := mkConst ``False, proof? := mkAppN (mkConst ``eqFalseOfDecide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }
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
  return Step.visit (← rewrite e lemmas.pre discharge? (tag := "pre"))

def rewritePost (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  let lemmas ← (← read).simpLemmas
  return Step.visit (← rewrite e lemmas.post discharge? (tag := "post"))

def preDefault (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step :=
  tryRewriteCtorEq e <| rewritePre e discharge?

def postDefault (e : Expr) (discharge? : Expr → SimpM (Option Expr)) : SimpM Step := do
  -- TODO: try equation lemmas
  tryRewriteCtorEq e <| tryRewriteUsingDecide e <| rewritePost e discharge?

end Lean.Meta.Simp
