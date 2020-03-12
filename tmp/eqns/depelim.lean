import Init.Lean

open Lean

inductive Pattern
| Inaccessible (e : Expr)
| Var          (fvarId : FVarId)
| Ctor         (fields : List Pattern)
| Val          (e : Expr)
| ArrayLit     (xs : List Pattern)

structure AltLHS :=
(fvarIds  : List FVarId)  -- free variables used in the patterns
(patterns : List Pattern) -- We use `List Pattern` since we have nary match-expressions.

abbrev AltToMinorsMap := PersistentHashMap Nat (List Nat)

structure ElimResult :=
(numMinors : Nat)  -- It is the number of alternatives (Reason: support for overlapping equations)
(numEqs    : Nat)  -- It is the number of minors (Reason: users may want equations that hold definitionally)
(elim      : Expr) -- The eliminator. It is not just `Expr.const elimName` because the type of the major premises may contain free variables.
(altMap    : AltToMinorsMap) -- each alternative may be "expanded" into multiple minor premise


/-
Given a list of major premises `xs` and alternative left-hand-sides, generate an elimination
principle with name `elimName` and equation lemmas for it.
-/
-- def mkElim (elimName : Name) (xs : List FVarId) (lhss : List AltLHS) : MetaM ElimResult :=
-- sorry

universes u v

inductive Vec (α : Type u) : Nat → Type u
| nil  {} : Vec 0
| cons    : α → forall {n : Nat}, Vec n → Vec (n+1)

def Vec.elim {α : Type u} (C : forall (n : Nat), Vec α n → Vec α n → Sort v) {n : Nat} (v w : Vec α n)
  (h₁ : Unit → C 0 Vec.nil Vec.nil)
  (h₂ : forall (hdv : α) (n : Nat) (tlv : Vec α n) (hdw : α) (tlw : Vec α n), C (n+1) (Vec.cons hdv tlv) (Vec.cons hdw tlw))
  : C n v w :=
match n, v, w with
| .(0),   Vec.nil,                   Vec.nil                    => h₁ ()
| .(n+1), @Vec.cons .(α) hdv n tlv, @Vec.cons .(α) hdw .(n) tlw => h₂ hdv n tlv hdw tlw

def Vec.elimHEq {α : Type u} (C : forall (n : Nat) (v w : Vec α n), Sort v) {n : Nat} (v w : Vec α n)
  (h₁ : v ≅ @Vec.nil α → w ≅ @Vec.nil α → C 0 Vec.nil Vec.nil)
  (h₂ : forall (hdv : α) (n : Nat) (tlv : Vec α n) (hdw : α) (tlw : Vec α n), v ≅ Vec.cons hdv tlv → w ≅ Vec.cons hdw tlw → C (n+1) (Vec.cons hdv tlv) (Vec.cons hdw tlw))
  : C n v w :=
Vec.elim (fun n' v' w' => v ≅ v' → w ≅ w' → C n' v' w') v w
  (fun _ => h₁)
  h₂
  (HEq.refl _)
  (HEq.refl _)

def Vec.elimEq {α : Type u} (C : forall (n : Nat) (v w : Vec α n), Sort v) {n : Nat} (v w : Vec α n)
  (h₁ : forall (h : n = 0), (Eq.rec v h : Vec α 0) = Vec.nil → (Eq.rec w h : Vec α 0) = Vec.nil → C 0 Vec.nil Vec.nil)
  (h₂ : forall (hdv : α) (n' : Nat) (tlv : Vec α n')
               (hdw : α) (tlw : Vec α n')
               (h : n = n' + 1),
               (Eq.rec v h : Vec α (n'+1)) = Vec.cons hdv tlv →
               (Eq.rec w h : Vec α (n'+1)) = Vec.cons hdw tlw →
               C (n'+1) (Vec.cons hdv tlv) (Vec.cons hdw tlw))
  : C n v w :=
Vec.elim (fun n' v' w' => forall (h : n = n'), (Eq.rec v h : Vec α n') = v' → (Eq.rec w h : Vec α n') = w' → C n' v' w') v w
  (fun _ => h₁)
  h₂
  rfl
  rfl
  rfl

def List.elim {α : Type u} (C : List α → Sort v) (as : List α)
  (h₁ : Unit → C [])
  (h₂ : forall a, C [a])
  (h₃ : forall (a₁ : α) (as₁ : List α) (a₂ : α) (as₂ : List α), as₁ = a₂ :: as₂ → C (a₁::a₂::as₂))
  : C as :=
List.casesOn as
  (h₁ ())
  (fun a r => @List.casesOn _ (fun as => r = as → C (a::as)) r
    (fun _ => h₂ a)
    (fun b bs h => h₃ a r b bs h) rfl)
