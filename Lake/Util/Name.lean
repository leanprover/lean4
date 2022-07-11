/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Name
import Lake.Util.Compare

open Lean

namespace Lake

export Lean (Name NameMap)

-- # Name Helpers

namespace Name

def ofString (str : String) : Name :=
  str.splitOn "." |>.foldl (fun n p => .str n p.trim) .anonymous

@[simp] protected theorem beq_false (m n : Name) : (m == n) = false ↔ ¬ (m = n) := by
  rw [← beq_iff_eq m n]; cases m == n <;> simp

@[simp] theorem isPrefixOf_self {n : Name} : n.isPrefixOf n := by
  cases n <;> simp [Name.isPrefixOf]

@[simp] theorem isPrefixOf_append {n m : Name} : n.isPrefixOf (n ++ m) := by
  show n.isPrefixOf (n.append m)
  induction m <;> simp [Name.isPrefixOf, Name.append, *]

attribute [local simp] Name.quickCmpAux

@[simp]
theorem quickCmpAux_iff_eq : ∀ n n', Name.quickCmpAux n n' = Ordering.eq ↔ n = n'
  | .anonymous, n => by cases n <;> simp
  | n, .anonymous => by cases n <;> simp
  | .num .., .str .. => by simp
  | .str .., .num .. => by simp
  | .num p₁ n₁, .num p₂ n₂ => by
    simp only [Name.quickCmpAux]; split <;>
    simp_all [quickCmpAux_iff_eq p₁ p₂, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]
  | .str p₁ s₁, .str p₂ s₂ => by
    simp only [Name.quickCmpAux]; split <;>
    simp_all [quickCmpAux_iff_eq p₁ p₂, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]

theorem eq_of_quickCmpAux (n n') : Name.quickCmpAux n n' = Ordering.eq → n = n' :=
  (quickCmpAux_iff_eq n n').1

end Name

-- # Subtype Helpers

namespace Subtype

theorem val_eq_of_eq {a b : Subtype p} (h : a = b) : a.val = b.val :=
  h ▸ rfl

theorem eq_of_val_eq : ∀ {a b : Subtype p}, a.val = b.val → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eq_iff_val_eq {a b : Subtype p} : a = b ↔ a.val = b.val :=
  Iff.intro val_eq_of_eq eq_of_val_eq

theorem ne_of_val_ne {a b : Subtype p} (h : a.val ≠ b.val) : a ≠ b :=
  fun h' => absurd (val_eq_of_eq h') h

theorem val_ne_of_ne {a b : Subtype p} (h : a ≠ b) : a.val ≠ b.val :=
  fun h' => absurd (eq_of_val_eq h') h

theorem ne_iff_val_ne {a b : Subtype p} : a ≠ b ↔ a.val ≠ b.val :=
  Iff.intro val_ne_of_ne ne_of_val_ne

end Subtype

theorem eq_of_quickCmp {n n' : Name} : n.quickCmp n' = Ordering.eq → n = n' := by
  simp only [Lean.Name.quickCmp, Name.quickCmp, Subtype.eq_iff_val_eq]
  intro h_cmp; split at h_cmp
  next => exact Name.eq_of_quickCmpAux n n' h_cmp
  next => contradiction

instance : EqOfCmp Name Name.quickCmp where
  eq_of_cmp h := eq_of_quickCmp h

open Syntax

def quoteNameFrom (ref : Syntax) : Name → Term
| .anonymous => mkCIdentFrom ref ``Name.anonymous
| .str p s => mkApp (mkCIdentFrom ref ``Name.mkStr)
  #[quoteNameFrom ref p, quote s]
| .num p v => mkApp (mkCIdentFrom ref ``Name.mkNum)
  #[quoteNameFrom ref p, quote v]
