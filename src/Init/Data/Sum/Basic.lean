/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
prelude
import Init.PropLemmas

/-!
# Disjoint union of types

This file defines basic operations on the the sum type `α ⊕ β`.

`α ⊕ β` is the type made of a copy of `α` and a copy of `β`. It is also called *disjoint union*.

## Main declarations

* `Sum.isLeft`: Returns whether `x : α ⊕ β` comes from the left component or not.
* `Sum.isRight`: Returns whether `x : α ⊕ β` comes from the right component or not.
* `Sum.getLeft`: Retrieves the left content of a `x : α ⊕ β` that is known to come from the left.
* `Sum.getRight`: Retrieves the right content of `x : α ⊕ β` that is known to come from the right.
* `Sum.getLeft?`: Retrieves the left content of `x : α ⊕ β` as an option type or returns `none`
  if it's coming from the right.
* `Sum.getRight?`: Retrieves the right content of `x : α ⊕ β` as an option type or returns `none`
  if it's coming from the left.
* `Sum.map`: Maps `α ⊕ β` to `γ ⊕ δ` component-wise.
* `Sum.elim`: Nondependent eliminator/induction principle for `α ⊕ β`.
* `Sum.swap`: Maps `α ⊕ β` to `β ⊕ α` by swapping components.
* `Sum.LiftRel`: The disjoint union of two relations.
* `Sum.Lex`: Lexicographic order on `α ⊕ β` induced by a relation on `α` and a relation on `β`.

## Further material

See `Init.Data.Sum.Lemmas` for theorems about these definitions.

## Notes

The definition of `Sum` takes values in `Type _`. This effectively forbids `Prop`- valued sum types.
To this effect, we have `PSum`, which takes value in `Sort _` and carries a more complicated
universe signature in consequence. The `Prop` version is `Or`.
-/

namespace Sum

deriving instance DecidableEq for Sum
deriving instance BEq for Sum

section get

/-- Check if a sum is `inl`. -/
def isLeft : α ⊕ β → Bool
  | inl _ => true
  | inr _ => false

/-- Check if a sum is `inr`. -/
def isRight : α ⊕ β → Bool
  | inl _ => false
  | inr _ => true

/-- Retrieve the contents from a sum known to be `inl`.-/
def getLeft : (ab : α ⊕ β) → ab.isLeft → α
  | inl a, _ => a

/-- Retrieve the contents from a sum known to be `inr`.-/
def getRight : (ab : α ⊕ β) → ab.isRight → β
  | inr b, _ => b

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
def getLeft? : α ⊕ β → Option α
  | inl a => some a
  | inr _ => none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
def getRight? : α ⊕ β → Option β
  | inr b => some b
  | inl _ => none

@[simp] theorem isLeft_inl : (inl x : α ⊕ β).isLeft = true := rfl
@[simp] theorem isLeft_inr : (inr x : α ⊕ β).isLeft = false := rfl
@[simp] theorem isRight_inl : (inl x : α ⊕ β).isRight = false := rfl
@[simp] theorem isRight_inr : (inr x : α ⊕ β).isRight = true := rfl

@[simp] theorem getLeft_inl (h : (inl x : α ⊕ β).isLeft) : (inl x).getLeft h = x := rfl
@[simp] theorem getRight_inr (h : (inr x : α ⊕ β).isRight) : (inr x).getRight h = x := rfl

@[simp] theorem getLeft?_inl : (inl x : α ⊕ β).getLeft? = some x := rfl
@[simp] theorem getLeft?_inr : (inr x : α ⊕ β).getLeft? = none := rfl
@[simp] theorem getRight?_inl : (inl x : α ⊕ β).getRight? = none := rfl
@[simp] theorem getRight?_inr : (inr x : α ⊕ β).getRight? = some x := rfl

end get

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  fun x => Sum.casesOn x f g

@[simp] theorem elim_inl (f : α → γ) (g : β → γ) (x : α) :
    Sum.elim f g (inl x) = f x := rfl

@[simp] theorem elim_inr (f : α → γ) (g : β → γ) (x : β) :
    Sum.elim f g (inr x) = g x := rfl

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β' :=
  Sum.elim (inl ∘ f) (inr ∘ g)

@[simp] theorem map_inl (f : α → α') (g : β → β') (x : α) : (inl x).map f g = inl (f x) := rfl

@[simp] theorem map_inr (f : α → α') (g : β → β') (x : β) : (inr x).map f g = inr (g x) := rfl

/-- Swap the factors of a sum type -/
def swap : α ⊕ β → β ⊕ α := Sum.elim inr inl

@[simp] theorem swap_inl : swap (inl x : α ⊕ β) = inr x := rfl

@[simp] theorem swap_inr : swap (inr x : α ⊕ β) = inl x := rfl

section LiftRel

/-- Lifts pointwise two relations between `α` and `γ` and between `β` and `δ` to a relation between
`α ⊕ β` and `γ ⊕ δ`. -/
inductive LiftRel (r : α → γ → Prop) (s : β → δ → Prop) : α ⊕ β → γ ⊕ δ → Prop
  /-- `inl a` and `inl c` are related via `LiftRel r s` if `a` and `c` are related via `r`. -/
  | protected inl {a c} : r a c → LiftRel r s (inl a) (inl c)
  /-- `inr b` and `inr d` are related via `LiftRel r s` if `b` and `d` are related via `s`. -/
  | protected inr {b d} : s b d → LiftRel r s (inr b) (inr d)

@[simp] theorem liftRel_inl_inl : LiftRel r s (inl a) (inl c) ↔ r a c :=
  ⟨fun h => by cases h; assumption, LiftRel.inl⟩

@[simp] theorem not_liftRel_inl_inr : ¬LiftRel r s (inl a) (inr d) := nofun

@[simp] theorem not_liftRel_inr_inl : ¬LiftRel r s (inr b) (inl c) := nofun

@[simp] theorem liftRel_inr_inr : LiftRel r s (inr b) (inr d) ↔ s b d :=
  ⟨fun h => by cases h; assumption, LiftRel.inr⟩

instance {r : α → γ → Prop} {s : β → δ → Prop}
    [∀ a c, Decidable (r a c)] [∀ b d, Decidable (s b d)] :
    ∀ (ab : α ⊕ β) (cd : γ ⊕ δ), Decidable (LiftRel r s ab cd)
  | inl _, inl _ => decidable_of_iff' _ liftRel_inl_inl
  | inl _, inr _ => Decidable.isFalse not_liftRel_inl_inr
  | inr _, inl _ => Decidable.isFalse not_liftRel_inr_inl
  | inr _, inr _ => decidable_of_iff' _ liftRel_inr_inr

end LiftRel

section Lex

/-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`, otherwise use the
respective order on `α` or `β`. -/
inductive Lex (r : α → α → Prop) (s : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
  /-- `inl a₁` and `inl a₂` are related via `Lex r s` if `a₁` and `a₂` are related via `r`. -/
  | protected inl {a₁ a₂} (h : r a₁ a₂) : Lex r s (inl a₁) (inl a₂)
  /-- `inr b₁` and `inr b₂` are related via `Lex r s` if `b₁` and `b₂` are related via `s`. -/
  | protected inr {b₁ b₂} (h : s b₁ b₂) : Lex r s (inr b₁) (inr b₂)
  /-- `inl a` and `inr b` are always related via `Lex r s`. -/
  | sep (a b) : Lex r s (inl a) (inr b)

attribute [simp] Lex.sep

@[simp] theorem lex_inl_inl : Lex r s (inl a₁) (inl a₂) ↔ r a₁ a₂ :=
  ⟨fun h => by cases h; assumption, Lex.inl⟩

@[simp] theorem lex_inr_inr : Lex r s (inr b₁) (inr b₂) ↔ s b₁ b₂ :=
  ⟨fun h => by cases h; assumption, Lex.inr⟩

@[simp] theorem lex_inr_inl : ¬Lex r s (inr b) (inl a) := nofun

instance instDecidableRelSumLex [DecidableRel r] [DecidableRel s] : DecidableRel (Lex r s)
  | inl _, inl _ => decidable_of_iff' _ lex_inl_inl
  | inl _, inr _ => Decidable.isTrue (Lex.sep _ _)
  | inr _, inl _ => Decidable.isFalse lex_inr_inl
  | inr _, inr _ => decidable_of_iff' _ lex_inr_inr

end Lex

end Sum
