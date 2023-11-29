/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json
import Lean.Data.NameMap
import Lake.Util.DRBMap
import Lake.Util.RBArray
import Lake.Util.Compare

open Lean

namespace Lake

export Lean (Name NameMap)

@[inline] def NameMap.empty : NameMap α := RBMap.empty

instance : ForIn m (NameMap α) (Name × α) where
  forIn self init f := self.forIn init f

instance : Coe (RBMap Name α Name.quickCmp) (NameMap α) := ⟨id⟩

abbrev OrdNameMap α := RBArray Name α Name.quickCmp
@[inline] def OrdNameMap.empty : OrdNameMap α := RBArray.empty
@[inline] def mkOrdNameMap (α : Type) : OrdNameMap α := RBArray.empty

abbrev DNameMap α := DRBMap Name α Name.quickCmp
@[inline] def DNameMap.empty : DNameMap α := DRBMap.empty

instance [ToJson α] : ToJson (NameMap α) where
  toJson m := Json.obj <| m.fold (fun n k v => n.insert compare k.toString (toJson v)) .leaf

instance [FromJson α] : FromJson (NameMap α) where
  fromJson? j := do
    (← j.getObj?).foldM (init := {}) fun m k v =>
      let k := k.toName
      if k.isAnonymous then
        throw "expected name"
      else
        return m.insert k (← fromJson? v)

/-! # Name Helpers -/

namespace Name
open Lean.Name

@[simp] protected theorem beq_false (m n : Name) : (m == n) = false ↔ ¬ (m = n) := by
  rw [← beq_iff_eq m n]; cases m == n <;> simp (config := { decide := true })

@[simp] theorem isPrefixOf_self {n : Name} : n.isPrefixOf n := by
  cases n <;> simp [isPrefixOf]

@[simp] theorem isPrefixOf_append {n m : Name} : ¬ n.hasMacroScopes → ¬ m.hasMacroScopes → n.isPrefixOf (n ++ m) := by
  intro h1 h2
  show n.isPrefixOf (n.append m)
  simp_all [Name.append]
  clear h2; induction m <;> simp [*, Name.appendCore, isPrefixOf]

@[simp] theorem quickCmpAux_iff_eq : ∀ {n n'}, quickCmpAux n n' = .eq ↔ n = n'
| .anonymous, n => by cases n <;> simp [quickCmpAux]
| n, .anonymous => by cases n <;> simp [quickCmpAux]
| .num .., .str .. => by simp [quickCmpAux]
| .str .., .num .. => by simp [quickCmpAux]
| .num p₁ n₁, .num p₂ n₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]
| .str p₁ s₁, .str p₂ s₂ => by
  simp only [quickCmpAux]; split <;>
  simp_all [quickCmpAux_iff_eq, show ∀ p, (p → False) ↔ ¬ p from fun _ => .rfl]

instance : LawfulCmpEq Name quickCmpAux where
  eq_of_cmp := quickCmpAux_iff_eq.mp
  cmp_rfl := quickCmpAux_iff_eq.mpr rfl

theorem eq_of_quickCmp {n n' : Name} : n.quickCmp n' = .eq → n = n' := by
  unfold Name.quickCmp
  intro h_cmp; split at h_cmp
  next => exact eq_of_cmp h_cmp
  next => contradiction

theorem quickCmp_rfl {n : Name} : n.quickCmp n = .eq := by
  unfold Name.quickCmp
  split <;> exact cmp_rfl

instance : LawfulCmpEq Name Name.quickCmp where
  eq_of_cmp := eq_of_quickCmp
  cmp_rfl := quickCmp_rfl

open Syntax

def quoteFrom (ref : Syntax) : Name → Term
| .anonymous => mkCIdentFrom ref ``anonymous
| .str p s => mkApp (mkCIdentFrom ref ``mkStr) #[quoteFrom ref p, quote s]
| .num p v => mkApp (mkCIdentFrom ref ``mkNum) #[quoteFrom ref p, quote v]
