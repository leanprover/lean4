/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Assertion
universe u v
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Exception Postcondition Types

Heterogeneous lists of exception postconditions for monads with multiple exception layers.

An `EPost` is a type-level list that tracks postconditions for each exception type in a
monad transformer stack. For example, `ExceptT Nat (ExceptT String (StateM σ))` would use
`EPost⟨Nat → σ → Prop, String → σ → Prop⟩` to specify postconditions for both exception types.

## Overview

- `EPost.Nil` is the empty exception postcondition (no exceptions).
- `EPost.Cons eh et` pairs a head postcondition type `eh` with a tail `et`.
- `EPost⟨e₁, e₂, ...⟩` is notation for nested `EPost.Cons`.
- `epost⟨v₁, v₂, ...⟩` is notation for constructing exception postcondition values.
-/

namespace Std.Internal.Do

/-- The empty exception postcondition type, used when a monad has no exception layers. -/
structure EPost.Nil : Type

/-- A cons cell pairing a head exception postcondition type `eh` with a tail `et`.

For a monad with exception type `ε` over lattice `l`, the head `eh` is typically `ε → l`
and the tail `et` tracks remaining exception layers. -/
structure EPost.Cons (eh : Type u) (et : Type v) where
  /-- The head exception postcondition. -/
  head : eh
  /-- The tail exception postconditions. -/
  tail : et

attribute [simp] EPost.Cons.head EPost.Cons.tail

/-!
## Partial Order and Complete Lattice Instances

Exception postconditions are ordered componentwise: `p ⊑ q` iff each component of `p`
is below the corresponding component of `q`.
-/

/-- The trivial partial order on `EPost.Nil`: all values are equal. -/
instance : PartialOrder EPost.Nil where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm := fun {p q} _ _ => by cases p; cases q; rfl

/-- The trivial complete lattice on `EPost.Nil`. -/
instance : CompleteLattice EPost.Nil where
  has_sup _ := ⟨EPost.Nil.mk, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

/-- Componentwise partial order on `EPost.Cons`, via `PProd`. -/
instance [PartialOrder eh] [PartialOrder et] : PartialOrder (EPost.Cons eh et) where
  rel p q := (⟨p.head, p.tail⟩ : eh ×' et) ⊑ ⟨q.head, q.tail⟩
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm := fun {p q} h1 h2 => by
    have := PartialOrder.rel_antisymm (α := eh ×' et) h1 h2
    cases p; cases q; cases this; rfl

/-- Componentwise complete lattice on `EPost.Cons`, via `PProd`. -/
instance [CompleteLattice eh] [CompleteLattice et] : CompleteLattice (EPost.Cons eh et) where
  has_sup c :=
    let c' : (eh ×' et) → Prop := fun p => c ⟨p.1, p.2⟩
    let ⟨sup, hsup⟩ := CompleteLattice.has_sup c'
    ⟨⟨sup.1, sup.2⟩, fun q =>
      ⟨fun hq p hp => (hsup ⟨q.head, q.tail⟩).mp hq ⟨p.head, p.tail⟩ hp,
       fun h => (hsup ⟨q.head, q.tail⟩).mpr fun pp hpp => h ⟨pp.1, pp.2⟩ hpp⟩⟩

/-!
## Ordering Lemmas
-/

/-- Extract a head ordering from an `EPost.Cons` ordering. -/
theorem EPost.Cons.le_head [PartialOrder eh] [PartialOrder et]
    {p q : EPost.Cons eh et} (h : p ⊑ q) : p.head ⊑ q.head :=
  h.1

/-- Extract a tail ordering from an `EPost.Cons` ordering. -/
theorem EPost.Cons.le_tail [PartialOrder eh] [PartialOrder et]
    {p q : EPost.Cons eh et} (h : p ⊑ q) : p.tail ⊑ q.tail :=
  h.2

/-- An `EPost.Cons` value is below another if both components are below. -/
theorem EPost.Cons.mk_le [PartialOrder e] [PartialOrder e'] (eposth : e) (epostt : e') (epost : EPost.Cons e e') :
    eposth ⊑ epost.head →
    epostt ⊑ epost.tail →
    EPost.Cons.mk eposth epostt ⊑ epost :=
  fun hh ht => ⟨hh, ht⟩

/-- An `EPost.Cons` value is below another if both components are below. -/
theorem EPost.Cons.mk_le_tail [PartialOrder e] [PartialOrder e'] (epostt : e') (epost : EPost.Cons e e') :
    epostt ⊑ epost.tail →
    EPost.Cons.mk epost.head epostt ⊑ epost := by
  apply EPost.Cons.mk_le; rfl

/-- The unique `EPost.Nil` value is below any `EPost.Nil` value. -/
theorem EPost.Nil.le (epost : EPost.Nil) :
    EPost.Nil.mk ⊑ epost := by
  simp [PartialOrder.rel]

/-- The head component of the bottom `EPost.Cons` is the bottom element. Propositional (not
definitional), because `⊥` of a complete lattice is `csup ∅`, not a constructor application. -/
theorem EPost.Cons.head_bot {eh : Type u} {et : Type v}
    [CompleteLattice eh] [CompleteLattice et] :
    EPost.Cons.head (⊥ : EPost.Cons eh et) = (⊥ : eh) := by
  refine PartialOrder.rel_antisymm ?_ (bot_le _)
  have h : (⊥ : EPost.Cons eh et) ⊑ EPost.Cons.mk (⊥ : eh) (⊥ : et) := bot_le _
  exact EPost.Cons.le_head h

/-!
## Notation

- `EPost⟨e₁, e₂, ...⟩` builds an exception postcondition **type** (nested `EPost.Cons`).
- `epost⟨v₁, v₂, ...⟩` builds an exception postcondition **value** (nested `EPost.Cons.mk`).
-/

/-- Exception postcondition type notation: `EPost⟨ε₁ → l, ε₂ → l⟩` for nested `EPost.Cons`. -/
syntax "EPost⟨" term,* "⟩" : term
/-- Exception postcondition value notation: `epost⟨h₁, h₂⟩` for nested `EPost.Cons.mk`. -/
syntax "epost⟨" term,* "⟩" : term

macro_rules
  | `(EPost⟨⟩) => `(EPost.Nil)
  | `(EPost⟨$x⟩) => `(EPost.Cons $x EPost.Nil)
  | `(EPost⟨$x, $xs,*⟩) => `(EPost.Cons $x EPost⟨$xs,*⟩)
  | `(epost⟨⟩) => `(EPost.Nil.mk)
  | `(epost⟨$x⟩) => `(EPost.Cons.mk $x EPost.Nil.mk)
  | `(epost⟨$x, $xs,*⟩) => `(EPost.Cons.mk $x epost⟨$xs,*⟩)

/-- Pretty-print `EPost.Nil` as `EPost⟨⟩`. -/
@[app_unexpander EPost.Nil] meta def unexpandEPostNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(EPost⟨⟩)

/-- Pretty-print `EPost.Cons` as `EPost⟨e₁, e₂, ...⟩`. -/
@[app_unexpander EPost.Cons] meta def unexpandEPostCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(EPost⟨⟩) => `(EPost⟨$x⟩)
    | `(EPost⟨$y⟩) => `(EPost⟨$x, $y⟩)
    | `(EPost⟨$y, $ys,*⟩) => `(EPost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.Cons $x $xs)
  | _ => throw ()

/-- Pretty-print `EPost.Nil.mk` as `epost⟨⟩`. -/
@[app_unexpander EPost.Nil.mk] meta def unexpandEPostNilMk : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(epost⟨⟩)

/-- Pretty-print `EPost.Cons.mk` as `epost⟨v₁, v₂, ...⟩`. -/
@[app_unexpander EPost.Cons.mk] meta def unexpandEPostConsMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(epost⟨⟩) => `(epost⟨$x⟩)
    | `(epost⟨$y⟩) => `(epost⟨$x, $y⟩)
    | `(epost⟨$y, $ys,*⟩) => `(epost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.Cons.mk $x $xs)
  | _ => throw ()

end Std.Internal.Do
