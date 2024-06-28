/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Option.Lemmas

namespace Option

@[simp] theorem isSome_map (α : Type u) (β : Type v) (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> simp

@[simp] theorem get!_none [Inhabited α] : (none : Option α).get! = default := rfl
@[simp] theorem get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl

theorem get_eq_get! [Inhabited α] : (o : Option α) → {h : o.isSome} → o.get h = o.get!
  | some _, _ => rfl

theorem get_eq_getD {fallback : α} : (o : Option α) → {h : o.isSome} → o.get h = o.getD fallback
  | some _, _ => rfl

theorem some_get! [Inhabited α] : (o : Option α) → o.isSome → some (o.get!) = o
  | some _, _ => rfl

theorem get!_eq_getD_default [Inhabited α] (o : Option α) : o.get! = o.getD default := rfl

def or : Option α → Option α → Option α
  | o@(some _), _ => o
  | none, o => o

@[simp] theorem or_some {a : α} {o : Option α} : or (some a) o = some a := rfl
@[simp] theorem none_or (o : Option α) : or none o = o := rfl

theorem or_eq_bif {o o' : Option α} : or o o' = bif o.isSome then o else o' := by
  cases o <;> rfl

@[simp]
theorem isSome_or {o o' : Option α} : (or o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> rfl

@[simp]
theorem isNone_or {o o' : Option α} : (or o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> rfl

@[simp]
theorem or_eq_none {o o' : Option α} : or o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> simp

theorem or_eq_some {o o' : Option α} {a : α} :
    or o o' = some a ↔ o = some a ∨ (o = none ∧ o' = some a) := by
  cases o <;> simp

theorem or_assoc (o₁ o₂ o₃ : Option α) :
    or (or o₁ o₂) o₃ = or o₁ (or o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> rfl
instance : Std.Associative (or (α := α)) := ⟨or_assoc⟩

@[simp]
theorem or_none (o : Option α) : or o none = o := by
  cases o <;> rfl
instance : Std.LawfulIdentity (or (α := α)) none where
  left_id := none_or
  right_id := or_none

@[simp]
theorem or_self (o : Option α) : or o o = o := by
  cases o <;> rfl
instance : Std.IdempotentOp (or (α := α)) := ⟨or_self⟩

theorem or_eq_orElse (o o' : Option α) : or o o' = o.orElse (fun _ => o') := by
  cases o <;> rfl

theorem map_or (f : α → β) (o o' : Option α) : (o.or o').map f = (o.map f).or (o'.map f) := by
  cases o <;> rfl


end Option
