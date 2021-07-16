/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open Lean.PrettyPrinter

def checkDelab (e : Expr) (tgt? : Option Syntax) (name? : Option Name := none) : TermElabM Unit := do
  if e.hasMVar then throwError "[checkDelab] term has mvars, {e}"
  let stx ← delab (← getCurrNamespace) [] e
  match tgt? with
  | some tgt =>
    if toString (← PrettyPrinter.ppTerm stx) != toString (← PrettyPrinter.ppTerm tgt?.get!) then
      throwError "[checkDelab] missed target\n{← PrettyPrinter.ppTerm stx}\n!=\n{← PrettyPrinter.ppTerm tgt}\n\nExpr: {e}\nType: {← inferType e}"
  | _ => pure ()

  let e' ←
    try
      let e' ← elabTerm stx (some (← inferType e))
      synthesizeSyntheticMVarsNoPostponing
      let e' ← instantiateMVars e'
      let ⟨e', _⟩ ← levelMVarToParam e'
      throwErrorIfErrors
      e'
    catch ex => throwError "[checkDelab] failed to re-elaborate,\n{stx}\n{← ex.toMessageData.toString}"
  if e'.hasMVar then throwError "[checkDelab] elaborated term still has mvars\n\nSyntax: {stx}\n\nExpression: {e'}"
  if not (← isDefEq e e') then throwError "[checkDelab] roundtrip not structurally equal\n\nOriginal: {e}\n\nSyntax: {stx}\n\nNew: {e'}"

syntax (name := testDelabTD) "#testDelab " term " expecting " term : command

@[commandElab testDelabTD] def elabTestDelabTD : CommandElab
  | `(#testDelab $stx:term expecting $tgt:term) => liftTermElabM `delabTD do
     let e ← elabTerm stx none
     let ⟨e, _⟩ ← levelMVarToParam e
     let e ← instantiateMVars e
     checkDelab e (some tgt)
  | _ => throwUnsupportedSyntax

syntax (name := testDelabTDN) "#testDelabN " ident : command

@[commandElab testDelabTDN] def elabTestDelabTDN : CommandElab
  | `(#testDelabN $name:ident) => liftTermElabM `delabTD do
    let name := name.getId
    let [name] ← resolveGlobalConst name | throwError "cannot resolve name"
    let some cInfo ← (← getEnv).find? name | throwError "no decl for name"
    let some value ← pure cInfo.value? | throwError "decl has no value"
    checkDelab value none
  | _ => throwUnsupportedSyntax

-------------------------------------------------
-------------------------------------------------
-------------------------------------------------

universe u v

set_option pp.analyze true
set_option pp.proofs true
set_option pp.structureInstanceTypes true

#testDelab @Nat.brecOn (fun x => Nat) 0 (fun x ih => x)
  expecting Nat.brecOn (motive := fun x => Nat) 0 fun x ih => x

#testDelab @Nat.brecOn (fun x => ∀ (y : Nat), Nat) 0 (fun x ih => fun y => y + x)
  expecting Nat.brecOn (motive := fun x => Nat → Nat) 0 fun x ih y => y + x

#testDelab @Nat.brecOn (fun x => Nat → Nat) 0 (fun x ih => fun y => y + x) 0
  expecting Nat.brecOn (motive := fun x => Nat → Nat) 0 (fun x ih y => y + x) 0

#testDelab let xs := #[]; xs.push (5 : Nat)
  expecting let xs : Array Nat := #[]; Array.push xs 5

#testDelab let x := Nat.zero; x + Nat.zero
  expecting let x := Nat.zero; x + Nat.zero

def fHole (α : Type) (x : α) : α := x

#testDelab fHole Nat Nat.zero
  expecting fHole _ Nat.zero

def fPoly {α : Type u} (x : α) : α := x

#testDelab fPoly Nat.zero
  expecting fPoly Nat.zero

#testDelab fPoly (id Nat.zero)
  expecting fPoly (id Nat.zero)

def fPoly2 {α : Type u} {β : Type v} (x : α) : α := x

#testDelab @fPoly2 _ (Type 3) Nat.zero
  expecting fPoly2 (β := Type 3) Nat.zero

def fPolyInst {α : Type u} [Add α] : α → α → α := Add.add

#testDelab @fPolyInst Nat ⟨Nat.add⟩
  expecting fPolyInst

def fPolyNotInst {α : Type u} (inst : Add α) : α → α → α := Add.add

#testDelab @fPolyNotInst Nat ⟨Nat.add⟩
  expecting fPolyNotInst { add := Nat.add : Add Nat }

#testDelab (fun (x : Nat) => x) Nat.zero
  expecting (fun (x : Nat) => x) Nat.zero

#testDelab (fun (α : Type) (x : α) => x) Nat Nat.zero
  expecting (fun (α : Type) (x : α) => x) _ Nat.zero

#testDelab (fun {α : Type} (x : α) => x) Nat.zero
  expecting (fun {α : Type} (x : α) => x) Nat.zero

#testDelab ((@Add.mk Nat Nat.add).1 : Nat → Nat → Nat)
  expecting Add.add

class Foo (α : Type v) where foo : α

instance : Foo Bool := ⟨true⟩

#testDelab @Foo.foo Bool ⟨true⟩
  expecting Foo.foo

#testDelab @Foo.foo Bool ⟨false⟩
  expecting Foo.foo (self := { foo := false : Foo Bool })

axiom wild {α : Type u} {f : α → Type v} {x : α} [_inst_1 : Foo (f x)] : Nat

abbrev nat2bool : Nat → Type := fun _ => Bool

#testDelab @wild Nat nat2bool Nat.zero ⟨false⟩
  expecting wild (α := Nat) (f := nat2bool) (x := Nat.zero) (_inst_1 := { foo := false : Foo (nat2bool Nat.zero) })

#testDelab @wild Nat (fun (n : Nat) => Bool) Nat.zero ⟨false⟩
  expecting wild (α := Nat) (f := fun n => Bool) (x := Nat.zero) (_inst_1 := { foo := false : Foo Bool })

#testDelab (fun {α : Type u} (x : α) => x : ∀ {α : Type u}, α → α)
  expecting fun x => x

#testDelab (fun {α : Type} (x : α) => x) Nat.zero
  expecting (fun {α : Type} (x : α) => x) Nat.zero

#testDelab (fun {α : Type} [Add α] (x : α) => x + x) (0 : Nat)
  expecting (fun {α : Type} [Add α] (x : α) => x + x) 0

#testDelab (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero
  expecting (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero

#testDelab id id id id Nat.zero
  expecting id id id id Nat.zero

#testDelab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => hxy ▸ hyz

set_option pp.analyze.trustSubst false in
#testDelab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => Eq.ndrec (a := x) (motive := fun x => x = z) hyz hxy

#testDelabN Nat.brecOn
#testDelabN Nat.below
#testDelabN Nat.mod_lt
#testDelabN Array.qsort
#testDelabN List.partition
#testDelabN List.partitionAux
