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
  let stx ← delab (← getCurrNamespace) (← getOpenDecls) e
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
      -- let ⟨e', _⟩ ← levelMVarToParam e'
      throwErrorIfErrors
      e'
    catch ex => throwError "[checkDelab] failed to re-elaborate,\n{stx}\n{← ex.toMessageData.toString}"

  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `pp.all true }) do
    if not (← isDefEq e e') then
      println! "[checkDelab] {← inferType e} {← inferType e'}"
      throwError "[checkDelab] roundtrip not structurally equal\n\nOriginal: {e}\n\nSyntax: {stx}\n\nNew: {e'}"

  let e' ← instantiateMVars e'
  if e'.hasMVar then throwError "[checkDelab] elaborated term still has mvars\n\nSyntax: {stx}\n\nExpression: {e'}"


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
    modify fun s => { s with levelNames := cInfo.levelParams }
    withTheReader Core.Context (fun ctx => { ctx with currNamespace := name.getPrefix, openDecls := [] }) do
      checkDelab value none
  | _ => throwUnsupportedSyntax

-------------------------------------------------
-------------------------------------------------
-------------------------------------------------

universe u v

set_option pp.analyze true

#testDelab @Nat.brecOn (fun x => Nat) 0 (fun x ih => x)
  expecting Nat.brecOn (motive := fun x => Nat) 0 fun x ih => x

#testDelab @Nat.brecOn (fun x => Nat → Nat) 0 (fun x ih => fun y => y + x)
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
  expecting wild (f := nat2bool) (x := Nat.zero) (_inst_1 := { foo := false : Foo (nat2bool Nat.zero) })

#testDelab @wild Nat (fun (n : Nat) => Bool) Nat.zero ⟨false⟩
  expecting wild (f := fun n => Bool) (x := Nat.zero) (_inst_1 := { foo := false : Foo Bool })

#testDelab (fun {α : Type u} (x : α) => x : ∀ {α : Type u}, α → α)
  expecting fun {α} x => x

#testDelab (fun {α : Type} (x : α) => x) Nat.zero
  expecting (fun {α : Type} (x : α) => x) Nat.zero

#testDelab (fun {α : Type} [Add α] (x : α) => x + x) (0 : Nat)
  expecting (fun {α : Type} [Add α] (x : α) => x + x) 0

#testDelab (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero
  expecting (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero

#testDelab id id id id Nat.zero
  expecting id id id id Nat.zero

def zzz : Unit := ()
def Z1.zzz : Unit := ()
def Z1.Z2.zzz : Unit := ()

namespace Z1.Z2

#testDelab _root_.zzz
  expecting _root_.zzz

#testDelab Z1.zzz
  expecting Z1.zzz

#testDelab zzz
  expecting zzz

end Z1.Z2

#testDelab fun {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (f : σ → α × σ) (s : σ) => pure (f := m) (f s)
  expecting fun {σ} {m} [Monad m] {α} f s => pure (f s)

set_option pp.analyze.trustSubst false in
#testDelab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => Eq.ndrec (a := x) (motive := fun x => x = z) hyz hxy

set_option pp.analyze.trustSubst true in
#testDelab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => hxy ▸ hyz

def fooReadGetModify : ReaderT Unit (StateT Unit IO) Unit := do
  let _ ← read
  let _ ← get
  modify fun s => s

#testDelab
  (do discard read
      pure () : ReaderT Bool IO Unit)
  expecting
    do discard read
       pure ()

#testDelab
  ((do let ctx ← read
       let s ← get
       modify fun s => s : ReaderT Bool (StateT Bool IO) Unit))
  expecting
  do let _ ← read
     let _ ← get
     modify fun s => s

#testDelabN Nat.brecOn
#testDelabN Nat.below
#testDelabN Nat.mod_lt
#testDelabN Array.qsort
#testDelabN List.partition
#testDelabN List.partitionAux
#testDelabN StateT.modifyGet
#testDelabN Nat.gcd_one_left
#testDelabN List.hasDecidableLt
#testDelabN Lean.Xml.parse
#testDelabN Add.noConfusionType
#testDelabN List.filterMapM.loop
#testDelabN instMonadReaderOf
#testDelabN instInhabitedPUnit
#testDelabN Lean.Syntax.getOptionalIdent?
#testDelabN Lean.Meta.ppExpr
#testDelabN Eq.mprProp

-- TODO: this test is broken because of the inability to solve structural max constraints
-- (See https://github.com/leanprover/lean4/issues/590)
-- #testDelabN Lean.PrefixTree.empty
-- #testDelabN Std.PersistentHashMap.getCollisionNodeSize.match_1
-- #testDelabN Std.HashMap.size.match_1

-- TODO: this is broken because it is currently inaccessible names
-- #testDelabN Std.ShareCommon.ObjectMap.find?
-- #testDelabN Std.ShareCommon.ObjectMap.insert

-- TODO: these all fail currently because of implicit lambdas
-- #testDelabN MonadLift.noConfusion
-- #testDelabN MonadLift.noConfusionType
-- #testDelabN MonadExcept.noConfusion
-- #testDelabN MonadFinally.noConfusion

-- TODO: these fail because we are not disable named patterns when not using `match` syntax
-- #testDelabN Lean.Elab.InfoTree.goalsAt?.match_1
