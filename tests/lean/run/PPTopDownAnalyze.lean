/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command
open Lean.PrettyPrinter

def checkDelab (e : Expr) (tgt? : Option Term) (name? : Option Name := none) : TermElabM Unit := do
  let pfix := "[checkDelab" ++ (match name? with | some n => ("." ++ toString n) | none => "") ++ "]"
  if e.hasMVar then throwError "{pfix} original term has mvars, {e}"
  let stx ← delab e
  match tgt? with
  | some tgt =>
    if toString (← PrettyPrinter.ppTerm stx) != toString (← PrettyPrinter.ppTerm tgt?.get!) then
      throwError "{pfix} missed target\n{← PrettyPrinter.ppTerm stx}\n!=\n{← PrettyPrinter.ppTerm tgt}\n\nExpr: {e}\nType: {← inferType e}"
  | _ => pure ()

  let e' ←
    try
      let e' ← elabTerm stx (some (← inferType e))
      synthesizeSyntheticMVarsNoPostponing
      let e' ← instantiateMVars e'
      -- let ⟨e', _⟩ ← levelMVarToParam e'
      throwErrorIfErrors
      pure e'
    catch ex => throwError "{pfix} failed to re-elaborate,\n{stx}\n{← ex.toMessageData.toString}"

  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `pp.all true }) do
    if not (← isDefEq e e') then
      println! "{pfix} {← inferType e} {← inferType e'}"
      throwError "{pfix} roundtrip not structurally equal\n\nOriginal: {e}\n\nSyntax: {stx}\n\nNew: {e'}"

  let e' ← instantiateMVars e'
  if e'.hasMVar then throwError "{pfix} elaborated term still has mvars\n\nSyntax: {stx}\n\nExpression: {e'}"


syntax (name := testDelabTD) "#test_delab " term " expecting " term : command

@[command_elab testDelabTD] def elabTestDelabTD : CommandElab
  | `(#test_delab $stx:term expecting $tgt:term) => liftTermElabM do withDeclName `delabTD do
     let e ← elabTerm stx none
     let e ← levelMVarToParam e
     let e ← instantiateMVars e
     checkDelab e (some tgt)
  | _ => throwUnsupportedSyntax

syntax (name := testDelabTDN) "#test_delab_n " ident : command

@[command_elab testDelabTDN] def elabTestDelabTDN : CommandElab
  | `(#test_delab_n $name:ident) => liftTermElabM do withDeclName `delabTD do
    let name := name.getId
    let [name] ← resolveGlobalConst (mkIdent name) | throwError "cannot resolve name"
    let some cInfo := (← getEnv).find? name | throwError "no decl for name"
    let some value ← pure cInfo.value? | throwError "decl has no value"
    modify fun s => { s with levelNames := cInfo.levelParams }
    withTheReader Core.Context (fun ctx => { ctx with currNamespace := name.getPrefix, openDecls := [] }) do
      checkDelab value none (some name)
  | _ => throwUnsupportedSyntax

-------------------------------------------------
-------------------------------------------------
-------------------------------------------------

universe u v

set_option pp.analyze true
set_option pp.analyze.checkInstances true
set_option pp.analyze.explicitHoles true
set_option pp.proofs true

#test_delab @Nat.brecOn (fun x => Nat) 0 (fun x ih => x)
  expecting Nat.brecOn (motive := fun x => Nat) 0 fun x ih => x

#test_delab @Nat.brecOn (fun x => Nat → Nat) 0 (fun x ih => fun y => y + x)
  expecting Nat.brecOn (motive := fun x => Nat → Nat) 0 fun x ih y => y + x

#test_delab @Nat.brecOn (fun x => Nat → Nat) 0 (fun x ih => fun y => y + x) 0
  expecting Nat.brecOn (motive := fun x => Nat → Nat) 0 (fun x ih y => y + x) 0

#test_delab let xs := #[]; xs.push (5 : Nat)
  expecting let xs : Array Nat := #[]; Array.push xs 5

#test_delab let x := Nat.zero; x + Nat.zero
  expecting let x := Nat.zero; x + Nat.zero

def fHole (α : Type) (x : α) : α := x

#test_delab fHole Nat Nat.zero
  expecting fHole _ Nat.zero

def fPoly {α : Type u} (x : α) : α := x

#test_delab fPoly Nat.zero
  expecting fPoly Nat.zero

#test_delab fPoly (id Nat.zero)
  expecting fPoly (id Nat.zero)

def fPoly2 {α : Type u} {β : Type v} (x : α) : α := x

#test_delab @fPoly2 _ (Type 3) Nat.zero
  expecting fPoly2 (β := Type 3) Nat.zero

def fPolyInst {α : Type u} [Add α] : α → α → α := Add.add

#test_delab @fPolyInst Nat ⟨Nat.add⟩
  expecting fPolyInst

def fPolyNotInst {α : Type u} (inst : Add α) : α → α → α := Add.add

#test_delab @fPolyNotInst Nat ⟨Nat.add⟩
  expecting fPolyNotInst { add := Nat.add }

#test_delab (fun (x : Nat) => x) Nat.zero
  expecting (fun (x : Nat) => x) Nat.zero

#test_delab (fun (α : Type) (x : α) => x) Nat Nat.zero
  expecting (fun (α : Type) (x : α) => x) _ Nat.zero

#test_delab (fun {α : Type} (x : α) => x) Nat.zero
  expecting (fun {α : Type} (x : α) => x) Nat.zero

#test_delab ((@Add.mk Nat Nat.add).1 : Nat → Nat → Nat)
  expecting Add.add

class Foo (α : Type v) where foo : α

instance : Foo Bool := ⟨true⟩

#test_delab @Foo.foo Bool ⟨true⟩
  expecting Foo.foo

#test_delab @Foo.foo Bool ⟨false⟩
  expecting Foo.foo (self := { foo := false })

axiom wild {α : Type u} {f : α → Type v} {x : α} [_inst_1 : Foo (f x)] : Nat

abbrev nat2bool : Nat → Type := fun _ => Bool

#test_delab @wild Nat nat2bool Nat.zero ⟨false⟩
  expecting wild (f := nat2bool) (x := Nat.zero) (_inst_1 := { foo := false })

#test_delab @wild Nat (fun (n : Nat) => Bool) Nat.zero ⟨false⟩
  expecting wild (f := fun n => Bool) (x := Nat.zero) (_inst_1 := { foo := false })

def takesFooUnnamed {Impl : Type} (Expl : Type) [Foo Nat] (x : Impl) (y : Expl) : Impl × Expl := (x, y)

#test_delab @takesFooUnnamed _ Nat (Foo.mk 7) false 5
  expecting @takesFooUnnamed _ _ { foo := 7 } false 5

#test_delab (fun {α : Type u} (x : α) => x : ∀ {α : Type u}, α → α)
  expecting fun {α} x => x

#test_delab (fun {α : Type} (x : α) => x) Nat.zero
  expecting (fun {α : Type} (x : α) => x) Nat.zero

#test_delab (fun {α : Type} [Add α] (x : α) => x + x) (0 : Nat)
  expecting (fun {α : Type} [Add α] (x : α) => x + x) 0

#test_delab (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero
  expecting (fun {α : Type} [Add α] (x : α) => x + x) Nat.zero

#test_delab id id id id Nat.zero
  expecting id id id id Nat.zero

def zzz : Unit := ()
def Z1.zzz : Unit := ()
def Z1.Z2.zzz : Unit := ()

namespace Z1.Z2

#test_delab _root_.zzz
  expecting _root_.zzz

#test_delab Z1.zzz
  expecting Z1.zzz

#test_delab zzz
  expecting zzz

end Z1.Z2

#test_delab fun {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (f : σ → α × σ) (s : σ) => pure (f := m) (f s)
  expecting fun {σ} {m} [Monad m] {α} f s => pure (f s)

set_option pp.analyze.trustSubst false in
#test_delab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => Eq.rec (motive := fun x_1 h => x_1 = z) hyz hxy

set_option pp.analyze.trustSubst true in
#test_delab (fun (x y z : Nat) (hxy : x = y) (hyz : x = z) => hxy ▸ hyz : ∀ (x y z : Nat), x = y → x = z → y = z)
  expecting fun x y z hxy hyz => hxy ▸ hyz

set_option pp.analyze.trustId true in
#test_delab Sigma.mk (β := fun α => α) Bool true
  expecting { fst := _, snd := true }

set_option pp.analyze.trustId false in
#test_delab Sigma.mk (β := fun α => α) Bool true
  expecting Sigma.mk (β := fun α => α) _ true

#test_delab let xs := #[true]; xs
  expecting let xs := #[true]; xs

def fooReadGetModify : ReaderT Unit (StateT Unit IO) Unit := do
  let _ ← read
  let _ ← get
  modify fun s => s

#test_delab
  (do discard read
      pure () : ReaderT Bool IO Unit)
  expecting
    do discard read
       pure ()

#test_delab
  ((do let ctx ← read
       let s ← get
       modify fun s => s : ReaderT Bool (StateT Bool IO) Unit))
  expecting
  do let _ ← read
     let _ ← get
     modify fun s => s

set_option pp.analyze.typeAscriptions true in
#test_delab (fun (x : Unit) => @id (ReaderT Bool IO Bool) (do read : ReaderT Bool IO Bool)) ()
  expecting (fun (x : Unit) => (id read : ReaderT Bool IO Bool)) ()

set_option pp.analyze.typeAscriptions false in
#test_delab (fun (x : Unit) => @id (ReaderT Bool IO Bool) (do read : ReaderT Bool IO Bool)) ()
  expecting (fun (x : Unit) => id read) ()

instance : CoeFun Bool (fun b => Bool → Bool) := { coe := fun b x => b && x }

#test_delab fun (xs : List Nat) => xs ≠ xs
  expecting fun xs => xs ≠ xs

structure S1 where x : Unit
structure S2 where x : Unit

#test_delab { x := () : S1 }
  expecting { x := () }

#test_delab (fun (u : Unit) => { x := () : S2 }) ()
  expecting (fun (u : Unit) => { x := () : S2 }) ()

#test_delab Eq.refl True
  expecting Eq.refl _

#test_delab (fun (u : Unit) => Eq.refl True) ()
  expecting  (fun (u : Unit) => Eq.refl True) ()

inductive NeedsAnalysis {α : Type} : Prop
  | mk : NeedsAnalysis

set_option pp.proofs false in
#test_delab @NeedsAnalysis.mk Unit
  expecting (_ : NeedsAnalysis (α := Unit))

set_option pp.proofs false in
set_option pp.proofs.withType false in
#test_delab @NeedsAnalysis.mk Unit
  expecting _

#test_delab ∀ (α : Type u) (vals vals_1 : List α), { data := vals : Array α } = { data := vals_1 : Array α }
  expecting ∀ (α : Type u) (vals vals_1 : List α), { data := vals : Array α } = { data := vals_1 }

#test_delab (do let ctxCore ← readThe Core.Context; pure ctxCore.currNamespace : MetaM Name)
  expecting do
    let ctxCore ← readThe Core.Context
    pure ctxCore.currNamespace

structure SubtypeLike1 {α : Sort u} (p : α → Prop) where

#test_delab SubtypeLike1 fun (x : Nat) => x < 10
  expecting SubtypeLike1 fun (x : Nat) => x < 10

#eval "prevent comment from parsing as part of previous expression"

--Note: currently we do not try "bottom-upping" inside lambdas
--(so we will always annotate the binder type)
#test_delab SubtypeLike1 fun (x : Nat) => Nat.succ x = x
  expecting SubtypeLike1 fun (x : Nat) => Nat.succ x = x

structure SubtypeLike3 {α β γ : Sort u} (p : α → β → γ → Prop) where

#test_delab SubtypeLike3 fun (x y z : Nat) => x + y < z
  expecting SubtypeLike3 fun (x y z : Nat) => x + y < z

structure SubtypeLike3Double {α β γ : Sort u} (p₁ : α → β → Prop) (p₂ : β → γ → Prop) where

#test_delab SubtypeLike3Double (fun (x y : Nat) => x = y) (fun (y z : Nat) => y = z)
  expecting SubtypeLike3Double (fun (x y : Nat) => x = y) fun y (z : Nat) => y = z

def takesStricts ⦃α : Type⦄ {β : Type} ⦃γ : Type⦄ : Unit := ()
#test_delab takesStricts expecting takesStricts
#test_delab @takesStricts expecting takesStricts
#test_delab @takesStricts Unit Unit expecting takesStricts (α := Unit) (β := Unit)
#test_delab @takesStricts Unit Unit Unit expecting takesStricts (α := Unit) (β := Unit) (γ := Unit)

def takesStrictMotive ⦃motive : Nat → Type⦄ {n : Nat} (x : motive n) : motive n := x
#test_delab takesStrictMotive expecting takesStrictMotive
#test_delab @takesStrictMotive (fun x => Unit) 0 expecting takesStrictMotive (motive := fun x => Unit) (n := 0)
#test_delab @takesStrictMotive (fun x => Unit) 0 () expecting takesStrictMotive (motive := fun x => Unit) (n := 0) ()

def arrayMkInjEqSnippet :=
  fun {α : Type} (xs : List α) => Eq.ndrec (motive := fun _ => (Array.mk xs = Array.mk xs)) (Eq.refl (Array.mk xs)) (rfl : xs = xs)

#test_delab_n arrayMkInjEqSnippet

def typeAs (α : Type u) (a : α) := ()

set_option pp.analyze.explicitHoles false in
#test_delab ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : (x : α) → β x}, (∀ (x : α), f₁ x = f₂ _) → f₁ = f₂
  expecting ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : (x : α) → β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂

set_option pp.analyze.trustSubtypeMk true in
#test_delab fun (n : Nat) (val : List Nat) (property : List.length val = n) => List.length { val := val, property := property : { x : List Nat // List.length x = n } }.val = n
  expecting fun n val property => List.length { val := val, property := property : { x : List Nat // List.length x = n } }.val = n

#test_delab_n Nat.brecOn
#test_delab_n Nat.below
#test_delab_n Nat.mod_lt
#test_delab_n Array.qsort
#test_delab_n List.partition
#test_delab_n List.partition.loop
#test_delab_n StateT.modifyGet
#test_delab_n Nat.gcd_one_left
#test_delab_n List.hasDecidableLT
#test_delab_n Lean.Xml.parse
#test_delab_n Add.noConfusionType
#test_delab_n List.filterMapM.loop
#test_delab_n instMonadReaderOf
#test_delab_n instInhabitedPUnit
#test_delab_n Lean.Syntax.getOptionalIdent?
#test_delab_n Lean.Meta.ppExpr
#test_delab_n MonadLift.noConfusion
#test_delab_n MonadLift.noConfusionType
#test_delab_n MonadExcept.noConfusion
#test_delab_n MonadFinally.noConfusion
#test_delab_n Lean.Elab.InfoTree.goalsAt?.match_1
#test_delab_n Array.mk.inj_eq
#test_delab_n Lean.PrefixTree.empty
#test_delab_n Lean.PersistentHashMap.getCollisionNodeSize.match_1
#test_delab_n Lean.HashMap.size.match_1
#test_delab_n and_false_eq

-- TODO: this one prints out a structure instance with keyword field `end`
set_option pp.structureInstances false in
#test_delab_n Lean.Server.FileWorker.handlePlainTermGoal

-- TODO: this one desugars to a `doLet` in an assignment
set_option pp.notation false in
#test_delab_n Lean.Server.FileWorker.handlePlainGoal

-- TODO: this error occurs because we use a term's type to determine `blockImplicit` (@),
-- whereas we should actually use the expected type based on the function being applied.
-- #test_delab_n HEq.subst

-- TODO: this error occurs because it cannot solve the universe constraints
-- (unclear if it is too few or too many annotations)
-- #test_delab_n ExceptT.seqRight_eq

-- TODO: this error occurs because a function has explicit binders while its type has
-- implicit binders. This may be an issue in the elaborator.
-- #test_delab_n Char.eqOfVeq
