/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.ReplaceS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.App
import Lean.Meta.AppBuilder
import Lean.Util.CollectFVars
namespace Lean.Meta.Sym.Simp

structure ToBetaAppResult where
  α : Expr
  u : Level
  e : Expr
  h : Expr
  varDeps : Array (Array Nat)
  deriving Inhabited

def collectFVarIdsAt (e : Expr) (fvarIdToPos : FVarIdMap Nat) : Array FVarId :=
  let s := collectFVars {} e
  let fvarIds := s.fvarIds.filter (fvarIdToPos.contains ·)
  fvarIds.qsort fun fvarId₁ fvarId₂ =>
    let pos₁ := fvarIdToPos.get! fvarId₁
    let pos₂ := fvarIdToPos.get! fvarId₂
    pos₁ < pos₂

def toBetaApp (haveExpr : Expr) : SymM ToBetaAppResult := do
  go haveExpr #[] #[] #[] #[] #[] {}
where
  go (e : Expr) (xs xs' args subst : Array Expr) (varDeps : Array (Array Nat)) (fvarIdToPos : FVarIdMap Nat)
      : SymM ToBetaAppResult := do
    if let .letE n t v b (nondep := true) := e then
      assert! !t.hasLooseBVars
      withLocalDeclD n t fun x => do
      let v := v.instantiateRev xs
      let fvarIds := collectFVarIdsAt v fvarIdToPos
      let varPos := fvarIds.map (fvarIdToPos.getD · 0)
      let ys := fvarIds.map mkFVar
      let arg ← mkLambdaFVars ys v
      withLocalDeclD n (← mkForallFVars ys t) fun x' => do
      let args' := fvarIds.map fun fvarId =>
        let pos := fvarIdToPos.get! fvarId
        subst[pos]!
      let v' := mkAppN x' args'
      let fvarIdToPos := fvarIdToPos.insert x.fvarId! xs.size
      go b (xs.push x) (xs'.push x') (args.push arg) (subst.push v') (varDeps.push varPos) fvarIdToPos
    else
      let e := e.instantiateRev subst
      let e ← mkLambdaFVars xs' e
      let e := mkAppN e args
      let α ← inferType haveExpr
      let u ← getLevel α
      let eq := mkApp3 (mkConst ``Eq [u]) α haveExpr e
      let h := mkApp2 (mkConst ``Eq.refl [u]) α haveExpr
      let h := mkExpectedPropHint h eq
      let e ← shareCommon e
      return { α, u, e, h, varDeps }

def consumeForallN (type : Expr) (n : Nat) : Expr :=
  match n with
  | 0 => type
  | n+1 => consumeForallN type.bindingBody! n

open Internal in
def elimAuxApps (e : Expr) (xs : Array Expr) (varDeps : Array (Array Nat)) : SymM Expr := do
  let n := xs.size
  replaceS e fun e offset => do
    if offset >= e.looseBVarRange then
      return some e
    match e.getAppFn with
    | .bvar idx =>
      if _h : idx >= offset then
        if _h : idx < offset + n then
          let i := n - (idx - offset) - 1
          let expectedNumArgs := varDeps[i]!.size
          let numArgs := e.getAppNumArgs
          if numArgs > expectedNumArgs then
            return none -- Over-applied
          else
            assert! numArgs == expectedNumArgs
            return xs[i]
        else
          mkBVarS (idx - n)
      else
        return some e
    | _ => return none

def toHave (e : Expr) (varDeps : Array (Array Nat)) : SymM Expr :=
  e.withApp fun f args => do
  if _h : args.size ≠ varDeps.size then unreachable! else
  let rec go (f : Expr) (xs : Array Expr) (i : Nat) : SymM Expr := do
    if _h : i < args.size then
      let .lam n t b _ := f | unreachable!
      let varPos := varDeps[i]
      let ys := varPos.map fun i => xs[i]!
      let type := consumeForallN t varPos.size
      let val ← share <| args[i].betaRev ys
      withLetDecl (nondep := true) n type val fun x => do
      go b (xs.push (← share x)) (i+1)
    else
      let f ← elimAuxApps f xs varDeps
      let result ← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) xs f
      share result
  go f #[] 0

def simpBetaApp (e : Expr) : SimpM Result := do
  match h : e with
  | .app f a => mkCongr e f a (← simpBetaApp f) (← simp a) h
  | e => simp e

public def simpHave (e : Expr) : SimpM Result := do
  let e₁ := e
  let r ← toBetaApp e₁
  let e₂ := r.e
  match (← simpBetaApp e₂) with
  | .rfl _ => return .rfl
  | .step e₃ h _ =>
    let h₁ := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₂ e₃ r.h h
    let e₄ ← toHave e₃ r.varDeps
    let eq := mkApp3 (mkConst ``Eq [r.u]) r.α e₃ e₄
    let h₂ := mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₃
    let h₂ := mkExpectedPropHint h₂ eq
    let h  := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₃ e₄ h₁ h₂
    return .step e₄ h

end Lean.Meta.Sym.Simp
