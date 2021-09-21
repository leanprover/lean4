/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SizeOf
import Init.Data.Nat.Basic

universe u v

set_option codegen false

inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

abbrev Acc.ndrec.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    {a : α} (n : Acc r a) : C a :=
Acc.rec (motive := fun α _ => C α) m n

abbrev Acc.ndrecOn.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    {a : α} (n : Acc r a)
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    : C a :=
Acc.rec (motive := fun α _ => C α) m n

namespace Acc
variable {α : Sort u} {r : α → α → Prop}

def inv {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y :=
Acc.recOn (motive := fun (x : α) _ => r y x → Acc r y)
  h₁ (fun x₁ ac₁ ih h₂ => ac₁ y h₂) h₂

end Acc

inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
  | intro (h : ∀ a, Acc r a) : WellFounded r

namespace WellFounded
def apply {α : Sort u} {r : α → α → Prop} (wf : WellFounded r) (a : α) : Acc r a :=
  WellFounded.recOn (motive := fun x => (y : α) → Acc r y)
    wf (fun p => p) a

section
variable {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)

theorem recursion {C : α → Sort v} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a := by
  induction (apply hwf a) with
  | intro x₁ ac₁ ih => exact h x₁ ih

theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a :=
  recursion hwf a h

variable {C : α → Sort v}
variable (F : ∀ x, (∀ y, r y x → C y) → C x)

def fixF (x : α) (a : Acc r x) : C x := by
  induction a with
  | intro x₁ ac₁ ih => exact F x₁ ih

def fixFEq (x : α) (acx : Acc r x) : fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) := by
  induction acx with
  | intro x r ih => exact rfl

end

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
def fix (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixF F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
theorem fix_eq (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) :
    fix hwf F x = F x (fun y h => fix hwf F y) :=
  fixFEq F x (apply hwf x)
end WellFounded

open WellFounded

-- Empty relation is well-founded
def emptyWf {α : Sort u} : WellFounded (@emptyRelation α) := by
  apply WellFounded.intro
  intro a
  apply Acc.intro a
  intro b h
  cases h

-- Subrelation of a well-founded relation is well-founded
namespace Subrelation
variable {α : Sort u} {r q : α → α → Prop}

def accessible {a : α} (h₁ : Subrelation q r) (ac : Acc r a) : Acc q a := by
  induction ac with
  | intro x ax ih =>
    apply Acc.intro
    intro y h
    exact ih y (h₁ h)

def wf (h₁ : Subrelation q r) (h₂ : WellFounded r) : WellFounded q :=
  ⟨fun a => accessible @h₁ (apply h₂ a)⟩
end Subrelation

-- The inverse image of a well-founded relation is well-founded
namespace InvImage
variable {α : Sort u} {β : Sort v} {r : β → β → Prop}

private def accAux (f : α → β) {b : β} (ac : Acc r b) : (x : α) → f x = b → Acc (InvImage r f) x := by
  induction ac with
  | intro x acx ih =>
    intro z e
    apply Acc.intro
    intro y lt
    subst x
    apply ih (f y) lt y rfl

def accessible {a : α} (f : α → β) (ac : Acc r (f a)) : Acc (InvImage r f) a :=
  accAux f ac a rfl

def wf (f : α → β) (h : WellFounded r) : WellFounded (InvImage r f) :=
  ⟨fun a => accessible f (apply h (f a))⟩
end InvImage

def invImage (f : α → β) (h : WellFounded r) : WellFounded (InvImage r f) :=
  InvImage.wf f h

-- The transitive closure of a well-founded relation is well-founded
namespace TC
variable {α : Sort u} {r : α → α → Prop}

def accessible {z : α} (ac : Acc r z) : Acc (TC r) z := by
  induction ac with
  | intro x acx ih =>
    apply Acc.intro x
    intro y rel
    induction rel with
    | base a b rab => exact ih a rab
    | trans a b c rab rbc ih₁ ih₂ => apply Acc.inv (ih₂ acx ih) rab

def wf (h : WellFounded r) : WellFounded (TC r) :=
  ⟨fun a => accessible (apply h a)⟩
end TC

-- less-than is well-founded
def Nat.lt_wf : WellFounded Nat.lt := by
  apply WellFounded.intro
  intro n
  induction n with
  | zero      =>
    apply Acc.intro 0
    intro _ h
    apply absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    apply Acc.intro (Nat.succ n)
    intro m h
    have : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)
    match this with
    | Or.inl e => subst e; assumption
    | Or.inr e => exact Acc.inv ih e

def Measure {α : Sort u} : (α → Nat) → α → α → Prop :=
  InvImage (fun a b => a < b)

def measure {α : Sort u} (f : α → Nat) : WellFounded (Measure f) :=
  invImage f Nat.lt_wf

def SizeofMeasure (α : Sort u) [SizeOf α] : α → α → Prop :=
  Measure sizeOf

def sizeofMeasure (α : Sort u) [SizeOf α] : WellFounded (SizeofMeasure α) :=
  measure sizeOf

namespace Prod
open WellFounded

section
variable {α : Type u} {β : Type v}
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)

-- Lexicographical order based on ra and rb
inductive Lex : α × β → α × β → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : Lex (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂)         : Lex (a, b₁)  (a, b₂)

-- relational product based on ra and rb
inductive RProd : α × β → α × β → Prop where
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : RProd (a₁, b₁) (a₂, b₂)
end

section

variable {α : Type u} {β : Type v}
variable {ra  : α → α → Prop} {rb  : β → β → Prop}

def lexAccessible (aca : (a : α) → Acc ra a) (acb : (b : β) → Acc rb b) (a : α) (b : β) : Acc (Lex ra rb) (a, b) := by
  induction (aca a) generalizing b with
  | intro xa aca iha =>
    induction (acb b) with
    | intro xb acb ihb =>
      apply Acc.intro (xa, xb)
      intro p lt
      cases lt with
      | left  _ _ h => apply iha _ h
      | right _ h   => apply ihb _ h

-- The lexicographical order of well founded relations is well-founded
def lex (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Lex ra rb) :=
  ⟨fun (a, b) => lexAccessible (WellFounded.apply ha) (WellFounded.apply hb) a b⟩

-- relational product is a Subrelation of the Lex
def RProdSubLex (a : α × β) (b : α × β) (h : RProd ra rb a b) : Lex ra rb a b := by
  cases h with
  | intro h₁ h₂ => exact Lex.left _ _ h₁

-- The relational product of well founded relations is well-founded
def rprod (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (RProd ra rb) := by
  apply Subrelation.wf (r := Lex ra rb) (h₂ := lex ha hb)
  intro a b h
  exact RProdSubLex a b h

end

end Prod

namespace PSigma
section
variable {α : Sort u} {β : α → Sort v}
variable  (r  : α → α → Prop)
variable  (s  : ∀ a, β a → β a → Prop)

-- Lexicographical order based on r and s
inductive Lex : PSigma β → PSigma β → Prop where
  | left  : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → Lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  | right : ∀ (a : α)  {b₁ b₂ : β a}, s a b₁ b₂ → Lex ⟨a, b₁⟩ ⟨a, b₂⟩
end

section
variable {α : Sort u} {β : α → Sort v}
variable {r  : α → α → Prop} {s : ∀ (a : α), β a → β a → Prop}

def lexAccessible {a} (aca : Acc r a) (acb : (a : α) → WellFounded (s a)) (b : β a) : Acc (Lex r s) ⟨a, b⟩ := by
  induction aca with
  | intro xa aca iha =>
    induction (WellFounded.apply (acb xa) b) with
    | intro xb acb ihb =>
      apply Acc.intro
      intro p lt
      cases lt with
      | left  => apply iha; assumption
      | right => apply ihb; assumption

-- The lexicographical order of well founded relations is well-founded
def lex (ha : WellFounded r) (hb : (x : α) → WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b
end

section
variable {α : Sort u} {β : Sort v}

def lexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r (fun a => s)

def lexNdepWf {r  : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) : WellFounded (lexNdep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) (fun x => hb) b
end

section
variable {α : Sort u} {β : Sort v}

-- Reverse lexicographical order based on r and s
inductive RevLex (r  : α → α → Prop) (s  : β → β → Prop) : @PSigma α (fun a => β) → @PSigma α (fun a => β) → Prop where
  | left  : {a₁ a₂ : α} → (b : β) → r a₁ a₂ → RevLex r s ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : (a₁ : α) → {b₁ : β} → (a₂ : α) → {b₂ : β} → s b₁ b₂ → RevLex r s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
open WellFounded
variable {α : Sort u} {β : Sort v}
variable {r  : α → α → Prop} {s : β → β → Prop}

def revLexAccessible {b} (acb : Acc s b) (aca : (a : α) → Acc r a): (a : α) → Acc (RevLex r s) ⟨a, b⟩ := by
  induction acb with
  | intro xb acb ihb =>
    intro a
    induction (aca a) with
    | intro xa aca iha =>
      apply Acc.intro
      intro p lt
      cases lt with
      | left  => apply iha; assumption
      | right => apply ihb; assumption

def revLex (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a
end

section
def SkipLeft (α : Type u) {β : Type v} (s : β → β → Prop) : @PSigma α (fun a => β) → @PSigma α (fun a => β) → Prop :=
  RevLex emptyRelation s

def skipLeft (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) : WellFounded (SkipLeft α s) :=
  revLex emptyWf hb

def mkSkipLeft {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α) (h : s b₁ b₂) : SkipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  RevLex.right _ _ h
end

end PSigma
