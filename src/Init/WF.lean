/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SizeOf
import Init.BinderNameHint
import Init.Data.Nat.Basic

universe u v

/--
`Acc` is the accessibility predicate. Given some relation `r` (e.g. `<`) and a value `x`,
`Acc r x` means that `x` is accessible through `r`:

`x` is accessible if there exists no infinite sequence `... < y₂ < y₁ < y₀ < x`.
-/
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  /--
  A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
  Note that if there exists no `y` such that `r y x`, then `x` is accessible. Such an `x` is called a
  _base case_.
  -/
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

noncomputable abbrev Acc.ndrec.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    {a : α} (n : Acc r a) : C a :=
  n.rec m

noncomputable abbrev Acc.ndrecOn.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1}
    {a : α} (n : Acc r a)
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    : C a :=
  n.rec m

namespace Acc
variable {α : Sort u} {r : α → α → Prop}

theorem inv {x y : α} (h₁ : Acc r x) (h₂ : r y x) : Acc r y :=
  h₁.recOn (fun _ ac₁ _ h₂ => ac₁ y h₂) h₂

end Acc

/--
A relation `r` is `WellFounded` if all elements of `α` are accessible within `r`.
If a relation is `WellFounded`, it does not allow for an infinite descent along the relation.

If the arguments of the recursive calls in a function definition decrease according to
a well founded relation, then the function terminates.
Well-founded relations are sometimes called _Artinian_ or said to satisfy the “descending chain condition”.
-/
inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
  | intro (h : ∀ a, Acc r a) : WellFounded r

class WellFoundedRelation (α : Sort u) where
  rel : α → α → Prop
  wf  : WellFounded rel

namespace WellFounded
theorem apply {α : Sort u} {r : α → α → Prop} (wf : WellFounded r) (a : α) : Acc r a :=
  wf.rec (fun p => p) a

section
variable {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)

noncomputable def recursion {C : α → Sort v} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a := by
  induction (apply hwf a) with
  | intro x₁ _ ih => exact h x₁ ih

include hwf in
theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a :=
  recursion hwf a h

variable {C : α → Sort v}
variable (F : ∀ x, (∀ y, r y x → C y) → C x)

noncomputable def fixF (x : α) (a : Acc r x) : C x := by
  induction a with
  | intro x₁ _ ih => exact F x₁ ih

theorem fixFEq (x : α) (acx : Acc r x) : fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) := by
  induction acx with
  | intro x r _ => exact rfl

end

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

-- Well-founded fixpoint
noncomputable def fix (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixF F x (apply hwf x)

-- Well-founded fixpoint satisfies fixpoint equation
theorem fix_eq (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) :
    fix hwf F x = F x (fun y _ => fix hwf F y) :=
  fixFEq F x (apply hwf x)
end WellFounded

open WellFounded

-- Empty relation is well-founded
def emptyWf {α : Sort u} : WellFoundedRelation α where
  rel := emptyRelation
  wf  := by
    apply WellFounded.intro
    intro a
    apply Acc.intro a
    intro b h
    cases h

-- Subrelation of a well-founded relation is well-founded
namespace Subrelation
variable {α : Sort u} {r q : α → α → Prop}

theorem accessible {a : α} (h₁ : Subrelation q r) (ac : Acc r a) : Acc q a := by
  induction ac with
  | intro x _ ih =>
    apply Acc.intro
    intro y h
    exact ih y (h₁ h)

theorem wf (h₁ : Subrelation q r) (h₂ : WellFounded r) : WellFounded q :=
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

theorem accessible {a : α} (f : α → β) (ac : Acc r (f a)) : Acc (InvImage r f) a :=
  accAux f ac a rfl

theorem wf (f : α → β) (h : WellFounded r) : WellFounded (InvImage r f) :=
  ⟨fun a => accessible f (apply h (f a))⟩
end InvImage

@[reducible] def invImage (f : α → β) (h : WellFoundedRelation β) : WellFoundedRelation α where
  rel := InvImage h.rel f
  wf  := InvImage.wf f h.wf

-- The transitive closure of a well-founded relation is well-founded
open Relation

theorem Acc.transGen (h : Acc r a) : Acc (TransGen r) a := by
  induction h with
  | intro x _ H =>
    refine Acc.intro x fun y hy ↦ ?_
    cases hy with
    | single hyx =>
      exact H y hyx
    | tail hyz hzx =>
      exact (H _ hzx).inv hyz

theorem acc_transGen_iff : Acc (TransGen r) a ↔ Acc r a :=
  ⟨Subrelation.accessible TransGen.single, Acc.transGen⟩

theorem WellFounded.transGen (h : WellFounded r) : WellFounded (TransGen r) :=
  ⟨fun a ↦ (h.apply a).transGen⟩

@[deprecated Acc.transGen (since := "2024-07-16")] abbrev TC.accessible := @Acc.transGen
@[deprecated WellFounded.transGen (since := "2024-07-16")] abbrev TC.wf := @WellFounded.transGen
namespace Nat

-- less-than is well-founded
def lt_wfRel : WellFoundedRelation Nat where
  rel := (· < ·)
  wf  := by
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

@[elab_as_elim] protected noncomputable def strongRecOn
    {motive : Nat → Sort u}
    (n : Nat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  Nat.lt_wfRel.wf.fix ind n

@[deprecated Nat.strongRecOn (since := "2024-08-27")]
protected noncomputable def strongInductionOn
    {motive : Nat → Sort u}
    (n : Nat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  Nat.strongRecOn n ind

@[elab_as_elim] protected noncomputable def caseStrongRecOn
    {motive : Nat → Sort u}
    (a : Nat)
    (zero : motive 0)
    (ind : ∀ n, (∀ m, m ≤ n → motive m) → motive (succ n)) : motive a :=
  Nat.strongRecOn a fun n =>
    match n with
    | 0   => fun _  => zero
    | n+1 => fun h₁ => ind n (λ _ h₂ => h₁ _ (lt_succ_of_le h₂))

@[deprecated Nat.caseStrongRecOn (since := "2024-08-27")]
protected noncomputable def caseStrongInductionOn
    {motive : Nat → Sort u}
    (a : Nat)
    (zero : motive 0)
    (ind : ∀ n, (∀ m, m ≤ n → motive m) → motive (succ n)) : motive a :=
  Nat.caseStrongRecOn a zero ind

end Nat

abbrev measure {α : Sort u} (f : α → Nat) : WellFoundedRelation α :=
  invImage f Nat.lt_wfRel

abbrev sizeOfWFRel {α : Sort u} [SizeOf α] : WellFoundedRelation α :=
  measure sizeOf

instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel

namespace Prod
open WellFounded

section
variable {α : Type u} {β : Type v}
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)

-- Lexicographical order based on ra and rb
protected inductive Lex : α × β → α × β → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) : Prod.Lex (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂)         : Prod.Lex (a, b₁)  (a, b₂)

theorem lex_def {r : α → α → Prop} {s : β → β → Prop} {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h => by cases h <;> simp [*], fun h =>
    match p, q, h with
    | _, _, Or.inl h => Lex.left _ _ h
    | (_, _), (_, _), Or.inr ⟨e, h⟩ => by subst e; exact Lex.right _ h⟩

namespace Lex

instance [αeqDec : DecidableEq α] {r : α → α → Prop} [rDec : DecidableRel r]
    {s : β → β → Prop} [sDec : DecidableRel s] : DecidableRel (Prod.Lex r s)
  | (a, b), (a', b') =>
    match rDec a a' with
    | isTrue raa' => isTrue $ left b b' raa'
    | isFalse nraa' =>
      match αeqDec a a' with
      | isTrue eq => by
        subst eq
        cases sDec b b' with
        | isTrue sbb' => exact isTrue $ right a sbb'
        | isFalse nsbb' =>
          apply isFalse; intro contra; cases contra <;> contradiction
      | isFalse neqaa' => by
        apply isFalse; intro contra; cases contra <;> contradiction

-- TODO: generalize
theorem right' {a₁ : Nat} {b₁ : β} (h₁ : a₁ ≤ a₂) (h₂ : rb b₁ b₂) : Prod.Lex Nat.lt rb (a₁, b₁) (a₂, b₂) :=
  match Nat.eq_or_lt_of_le h₁ with
  | Or.inl h => h ▸ Prod.Lex.right a₁ h₂
  | Or.inr h => Prod.Lex.left b₁ _ h

end Lex

-- relational product based on ra and rb
inductive RProd : α × β → α × β → Prop where
  | intro {a₁ b₁ a₂ b₂} (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) : RProd (a₁, b₁) (a₂, b₂)
end

section

variable {α : Type u} {β : Type v}
variable {ra  : α → α → Prop} {rb  : β → β → Prop}

theorem lexAccessible {a : α} (aca : Acc ra a) (acb : (b : β) → Acc rb b) (b : β) : Acc (Prod.Lex ra rb) (a, b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b) with
    | intro xb _ ihb =>
      apply Acc.intro (xa, xb)
      intro p lt
      cases lt with
      | left  _ _ h => apply iha _ h
      | right _ h   => apply ihb _ h

-- The lexicographical order of well founded relations is well-founded
@[reducible] def lex (ha : WellFoundedRelation α) (hb : WellFoundedRelation β) : WellFoundedRelation (α × β) where
  rel := Prod.Lex ha.rel hb.rel
  wf  := ⟨fun (a, b) => lexAccessible (WellFounded.apply ha.wf a) (WellFounded.apply hb.wf) b⟩

instance [ha : WellFoundedRelation α] [hb : WellFoundedRelation β] : WellFoundedRelation (α × β) :=
  lex ha hb

-- relational product is a Subrelation of the Lex
theorem RProdSubLex (a : α × β) (b : α × β) (h : RProd ra rb a b) : Prod.Lex ra rb a b := by
  cases h with
  | intro h₁ h₂ => exact Prod.Lex.left _ _ h₁

-- The relational product of well founded relations is well-founded
def rprod (ha : WellFoundedRelation α) (hb : WellFoundedRelation β) : WellFoundedRelation (α × β) where
  rel := RProd ha.rel hb.rel
  wf  := by
    apply Subrelation.wf (r := Prod.Lex ha.rel hb.rel) (h₂ := (lex ha hb).wf)
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

theorem lexAccessible {a} (aca : Acc r a) (acb : (a : α) → WellFounded (s a)) (b : β a) : Acc (Lex r s) ⟨a, b⟩ := by
  induction aca with
  | intro xa _ iha =>
    induction (WellFounded.apply (acb xa) b) with
    | intro xb _ ihb =>
      apply Acc.intro
      intro p lt
      cases lt with
      | left  => apply iha; assumption
      | right => apply ihb; assumption

-- The lexicographical order of well founded relations is well-founded
@[reducible] def lex (ha : WellFoundedRelation α) (hb : (a : α) → WellFoundedRelation (β a)) : WellFoundedRelation (PSigma β) where
  rel := Lex ha.rel (fun a => hb a |>.rel)
  wf  := WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha.wf a) (fun a => hb a |>.wf) b

instance [ha : WellFoundedRelation α] [hb : (a : α) → WellFoundedRelation (β a)] : WellFoundedRelation (PSigma β) :=
  lex ha hb

end

section
variable {α : Sort u} {β : Sort v}

def lexNdep (r : α → α → Prop) (s : β → β → Prop) :=
  Lex r (fun _ => s)

theorem lexNdepWf {r  : α → α → Prop} {s : β → β → Prop} (ha : WellFounded r) (hb : WellFounded s) : WellFounded (lexNdep r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) (fun _ => hb) b
end

section
variable {α : Sort u} {β : Sort v}

-- Reverse lexicographical order based on r and s
inductive RevLex (r  : α → α → Prop) (s  : β → β → Prop) : @PSigma α (fun _ => β) → @PSigma α (fun _ => β) → Prop where
  | left  : {a₁ a₂ : α} → (b : β) → r a₁ a₂ → RevLex r s ⟨a₁, b⟩ ⟨a₂, b⟩
  | right : (a₁ : α) → {b₁ : β} → (a₂ : α) → {b₂ : β} → s b₁ b₂ → RevLex r s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
end

section
open WellFounded
variable {α : Sort u} {β : Sort v}
variable {r  : α → α → Prop} {s : β → β → Prop}

theorem revLexAccessible {b} (acb : Acc s b) (aca : (a : α) → Acc r a): (a : α) → Acc (RevLex r s) ⟨a, b⟩ := by
  induction acb with
  | intro xb _ ihb =>
    intro a
    induction (aca a) with
    | intro xa _ iha =>
      apply Acc.intro
      intro p lt
      cases lt with
      | left  => apply iha; assumption
      | right => apply ihb; assumption

theorem revLex (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a
end

section
def SkipLeft (α : Type u) {β : Type v} (s : β → β → Prop) : @PSigma α (fun _ => β) → @PSigma α (fun _ => β) → Prop :=
  RevLex emptyRelation s

def skipLeft (α : Type u) {β : Type v} (hb : WellFoundedRelation β) : WellFoundedRelation (PSigma fun _ : α => β) where
  rel := SkipLeft α hb.rel
  wf  := revLex emptyWf.wf hb.wf

theorem mkSkipLeft {α : Type u} {β : Type v} {b₁ b₂ : β} {s : β → β → Prop} (a₁ a₂ : α) (h : s b₁ b₂) : SkipLeft α s ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ :=
  RevLex.right _ _ h
end

end PSigma

/--
The `wfParam` gadget is used internally during the construction of recursive functions by
wellfounded recursion, to keep track of the parameter for which the automatic introduction
of `List.attach` (or similar) is plausible.
-/
def wfParam {α : Sort u} (a : α) : α := a

/--
Reverse direction of `dite_eq_ite`. Used by the well-founded definition preprocessor to extend the
context of a termination proof inside `if-then-else` with the condition.
-/
@[wf_preprocess] theorem ite_eq_dite [Decidable P] :
    ite P a b = (dite P (fun h => binderNameHint h () a) (fun h => binderNameHint h () b)) := by
  rfl
