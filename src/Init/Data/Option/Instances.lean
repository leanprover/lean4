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
Equality with `none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to the standard instance of
`DecidableEq (Option α)`, which can cause problems. It can be locally bound if needed.

Try to use the Boolean comparisons `Option.isNone` or `Option.isSome` instead.
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
Given an optional value and a function that can be applied when the value is `some`, returns the
result of applying the function if this is possible.

The function `f` is _partial_ because it is only defined for the values `a : α` such `a ∈ o`, which
is equivalent to `o = some a`. This restriction allows the function to use the fact that it can only
be called when `o` is not `none`: it can relate its argument to the optional value `o`. Its runtime
behavior is equivalent to that of `Option.bind`.

Examples:
```lean example
def attach (v : Option α) : Option { y : α // y ∈ v } :=
  v.pbind fun x h => some ⟨x, h⟩
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
@[inline]
def pbind : (o : Option α) → (f : (a : α) → a ∈ o → Option β) → Option β
  | none, _ => none
  | some a, f => f a rfl

/--
Given a function from the elements of `α` that satisfy `p` to `β` and a proof that an optional value
satisfies `p` if it's present, applies the function to the value.

Examples:
```lean example
def attach (v : Option α) : Option { y : α // y ∈ v } :=
  v.pmap (fun a (h : a ∈ v) => ⟨_, h⟩) (fun _ h => h)
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
@[inline] def pmap {p : α → Prop}
    (f : ∀ a : α, p a → β) :
    (o : Option α) → (∀ a, a ∈ o → p a) → Option β
  | none, _ => none
  | some a, H => f a (H a rfl)

/--
Given an optional value and a function that can be applied when the value is `some`, returns the
result of applying the function if this is possible, or a fallback value otherwise.

The function `f` is _partial_ because it is only defined for the values `a : α` such `a ∈ o`, which
is equivalent to `o = some a`. This restriction allows the function to use the fact that it can only
be called when `o` is not `none`: it can relate its argument to the optional value `o`. Its runtime
behavior is equivalent to that of `Option.elim`.

Examples:
```lean example
def attach (v : Option α) : Option { y : α // y ∈ v } :=
  v.pelim none fun x h => some ⟨x, h⟩
```
```lean example
#reduce attach (some 3)
```
```output
some ⟨3, ⋯⟩
```
```lean example
#reduce attach none
```
```output
none
```
-/
@[inline] def pelim (o : Option α) (b : β) (f : (a : α) → a ∈ o → β) : β :=
  match o with
  | none => b
  | some a => f a rfl

/-- Partial filter. If `o : Option α`, `p : (a : α) → o = some a → Bool`, then `o.pfilter p` is
the same as `o.filter p` but `p` is passed the proof that `o = some a`. -/
@[inline] def pfilter (o : Option α) (p : (a : α) → o = some a → Bool) : Option α :=
  match o with
  | none => none
  | some a => bif p a rfl then o else none

/--
Executes a monadic action on an optional value if it is present, or does nothing if there is no
value.

Examples:
```lean example
#eval ((some 5).forM set : StateM Nat Unit).run 0
```
```output
((), 5)
```
```lean example
#eval (none.forM (fun x : Nat => set x) : StateM Nat Unit).run 0
```
```output
((), 0)
```
-/
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
