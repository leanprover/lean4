/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic

universe u v

namespace Option

theorem eq_of_eq_some {α : Type u} : ∀ {x y : Option α}, (∀z, x = some z ↔ y = some z) → x = y
  | none,   none,   _ => rfl
  | none,   some z, h => Option.noConfusion ((h z).2 rfl)
  | some z, none,   h => Option.noConfusion ((h z).1 rfl)
  | some _, some w, h => Option.noConfusion ((h w).2 rfl) (congrArg some)

theorem eq_none_of_isNone {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, _ => rfl

instance : Membership α (Option α) := ⟨fun b a => b = some a⟩

@[simp] theorem mem_def {a : α} {b : Option α} : a ∈ b ↔ b = some a := .rfl

instance [DecidableEq α] (j : α) (o : Option α) : Decidable (j ∈ o) :=
  inferInstanceAs <| Decidable (o = some j)

@[simp] theorem isNone_iff_eq_none {o : Option α} : o.isNone ↔ o = none :=
  ⟨Option.eq_none_of_isNone, fun e => e.symm ▸ rfl⟩

theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp; rfl

/--
`o = none` is decidable even if the wrapped type does not have decidable equality.
This is not an instance because it is not definitionally equal to `instance : DecidableEq Option`.
Try to use `o.isNone` or `o.isSome` instead.
-/
@[inline] def decidable_eq_none {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none

instance {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∀ a, a ∈ o → p a)
| none => isTrue nofun
| some a =>
  if h : p a then isTrue fun _ e => some_inj.1 e ▸ h
  else isFalse <| mt (· _ rfl) h

instance {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (Exists fun a => a ∈ o ∧ p a)
| none => isFalse nofun
| some a => if h : p a then isTrue ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ => h hn

/--
Partial bind. If for some `x : Option α`, `f : Π (a : α), a ∈ x → Option β` is a
partial function defined on `a : α` giving an `Option β`, where `some a = x`,
then `pbind x f h` is essentially the same as `bind x f`
but is defined only when all `x = some a`, using the proof to apply `f`.
-/
@[inline]
def pbind : ∀ x : Option α, (∀ a : α, a ∈ x → Option β) → Option β
  | none, _ => none
  | some a, f => f a rfl

/--
Partial map. If `f : Π a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f x h` is essentially the same as `map f x` but is defined only when all members of `x`
satisfy `p`, using the proof to apply `f`.
-/
@[inline] def pmap {p : α → Prop} (f : ∀ a : α, p a → β) :
    ∀ x : Option α, (∀ a, a ∈ x → p a) → Option β
  | none, _ => none
  | some a, H => f a (H a rfl)

/-- Partial elimination. If `o : Option α` and `f : (a : α) → a ∈ o → β`, then `o.pelim b f` is
the same as `o.elim b f` but `f` is passed the proof that `a ∈ o`. -/
@[inline] def pelim (o : Option α) (b : β) (f : (a : α) → a ∈ o → β) : β :=
  match o with
  | none => b
  | some a => f a rfl

/-- Map a monadic function which returns `Unit` over an `Option`. -/
@[inline] protected def forM [Pure m] : Option α → (α → m PUnit) → m PUnit
  | none  , _ => pure ⟨⟩
  | some a, f => f a

instance : ForM m (Option α) α :=
  ⟨Option.forM⟩

instance : ForIn' m (Option α) α inferInstance where
  forIn' x init f := do
    match x with
    | none => return init
    | some a =>
      match ← f a rfl init with
      | .done r | .yield r => return r

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

end Option
