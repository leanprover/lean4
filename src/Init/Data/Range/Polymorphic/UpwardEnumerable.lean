/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Option.Lemmas

public section

namespace Std.PRange

/--
This typeclass provides the function `succ? : α → Option α` that computes the successor of
elements of `α`, or none if no successor exists.
It also provides the function `succMany?`, which computes `n`-th successors.

`succ?` is expected to be acyclic: No element is its own transitive successor.
If `α` is ordered, then every element larger than `a : α` should be a transitive successor of `a`.
These properties and the compatibility of `succ?` with `succMany?` are encoded in the typeclasses
`LawfulUpwardEnumerable`, `LawfulUpwardEnumerableLE` and `LawfulUpwardEnumerableLT`.

-/
class UpwardEnumerable (α : Type u) where
  /-- Maps elements of `α` to their successor, or none if no successor exists. -/
  succ? : α → Option α
  /--
  Maps elements of `α` to their `n`-th successor, or none if no successor exists.
  This should semantically behave like repeatedly applying `succ?`, but it might be more efficient.

  `LawfulUpwardEnumerable` ensures the compatibility with `succ?`.

  If no other implementation is provided in `UpwardEnumerable` instance, `succMany?` repeatedly
  applies `succ?`.
  -/
  succMany? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

/--
According to `UpwardEnumerable.LE`, `a` is less than or equal to `b` if `b` is `a` or a transitive
successor of `a`.
-/
@[expose]
def UpwardEnumerable.LE {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? n a = some b

/--
According to `UpwardEnumerable.LT`, `a` is less than `b` if `b` is a proper transitive successor of
`a`. 'Proper' means that `b` is the `n`-th successor of `a`, where `n > 0`.

Given `LawfulUpwardEnumerable α`, no element of `α` is less than itself.
-/
@[expose]
def UpwardEnumerable.LT {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? (n + 1) a = some b

theorem UpwardEnumerable.le_of_lt {α : Type u} [UpwardEnumerable α] {a b : α}
    (h : UpwardEnumerable.LT a b) : UpwardEnumerable.LE a b :=
  ⟨h.choose + 1, h.choose_spec⟩

/--
The typeclass `Least? α` optionally provides a smallest element of `α`, `least? : Option α`.

The main use case of this typeclass is to use it in combination with `UpwardEnumerable` to
obtain a (possibly infinite) ascending enumeration of all elements of `α`.
-/
class Least? (α : Type u) where
  /--
  Returns the smallest element of `α`, or none if `α` is empty.

  Only empty types are allowed to define `least? := none`. If `α` is ordered and nonempty, then
  the value of `least?` should be the smallest element according to the order on `α`.
  -/
  least? : Option α

/--
This typeclass ensures that an `UpwardEnumerable α` instance is well-behaved.
-/
class LawfulUpwardEnumerable (α : Type u) [UpwardEnumerable α] where
  /-- There is no cyclic chain of successors. -/
  ne_of_lt (a b : α) : UpwardEnumerable.LT a b → a ≠ b
  /-- The `0`-th successor of `a` is `a` itself. -/
  succMany?_zero (a : α) : UpwardEnumerable.succMany? 0 a = some a
  /--
  The `n + 1`-th successor of `a` is the successor of the `n`-th successor, given that said
  successors actualy exist.
  -/
  succMany?_succ (n : Nat) (a : α) :
    UpwardEnumerable.succMany? (n + 1) a = (UpwardEnumerable.succMany? n a).bind UpwardEnumerable.succ?

theorem UpwardEnumerable.succMany?_zero [UpwardEnumerable α] [LawfulUpwardEnumerable α] {a : α} :
    UpwardEnumerable.succMany? 0 a = some a :=
  LawfulUpwardEnumerable.succMany?_zero a

theorem UpwardEnumerable.succMany?_succ [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Nat} {a : α} :
    UpwardEnumerable.succMany? (n + 1) a =
      (UpwardEnumerable.succMany? n a).bind UpwardEnumerable.succ? :=
  LawfulUpwardEnumerable.succMany?_succ n a

theorem UpwardEnumerable.succMany?_one [UpwardEnumerable α] [LawfulUpwardEnumerable α] {a : α} :
    UpwardEnumerable.succMany? 1 a = UpwardEnumerable.succ? a := by
  simp [UpwardEnumerable.succMany?_succ, UpwardEnumerable.succMany?_zero]

theorem UpwardEnumerable.succMany?_add [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (m n : Nat) (a : α) :
    UpwardEnumerable.succMany? (m + n) a =
      (UpwardEnumerable.succMany? m a).bind (UpwardEnumerable.succMany? n ·) := by
  induction n
  case zero => simp [LawfulUpwardEnumerable.succMany?_zero]
  case succ n ih =>
    rw [← Nat.add_assoc, LawfulUpwardEnumerable.succMany?_succ, ih, Option.bind_assoc]
    simp only [LawfulUpwardEnumerable.succMany?_succ]

theorem LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (n : Nat) (a : α) :
    UpwardEnumerable.succMany? (n + 1) a =
      (UpwardEnumerable.succ? a).bind (UpwardEnumerable.succMany? n ·) := by
  rw [Nat.add_comm]
  simp [UpwardEnumerable.succMany?_add, LawfulUpwardEnumerable.succMany?_succ,
    LawfulUpwardEnumerable.succMany?_zero]

theorem UpwardEnumerable.le_refl {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (a : α) : UpwardEnumerable.LE a a :=
  ⟨0, LawfulUpwardEnumerable.succMany?_zero a⟩

theorem UpwardEnumerable.le_trans {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b c : α} (hab : UpwardEnumerable.LE a b) (hbc : UpwardEnumerable.LE b c) :
    UpwardEnumerable.LE a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  simp [succMany?_add, hab.choose_spec, hbc.choose_spec]

theorem UpwardEnumerable.le_of_succ?_eq {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} (hab : UpwardEnumerable.succ? a = some b) : UpwardEnumerable.LE a b :=
  ⟨1, by simp [UpwardEnumerable.succMany?_one, hab]⟩

theorem UpwardEnumerable.lt_of_lt_of_le {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b c : α} (hab : UpwardEnumerable.LT a b) (hbc : UpwardEnumerable.LE b c) :
    UpwardEnumerable.LT a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  rw [Nat.add_right_comm, succMany?_add, hab.choose_spec, Option.bind_some, hbc.choose_spec]

theorem UpwardEnumerable.not_gt_of_le {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.LE a b → ¬ UpwardEnumerable.LT b a := by
  rintro ⟨n, hle⟩ ⟨m, hgt⟩
  have : UpwardEnumerable.LT a a := by
    refine ⟨n + m, ?_⟩
    rw [Nat.add_assoc, UpwardEnumerable.succMany?_add, hle, Option.bind_some, hgt]
  exact LawfulUpwardEnumerable.ne_of_lt _ _ this rfl

theorem UpwardEnumerable.not_gt_of_lt {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} (h : UpwardEnumerable.LT a b) : ¬ UpwardEnumerable.LT b a :=
  not_gt_of_le (le_of_lt h)

theorem UpwardEnumerable.ne_of_lt {α : Type w} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.LT a b → a ≠ b :=
  LawfulUpwardEnumerable.ne_of_lt a b

/--
This propositional typeclass ensures that `UpwardEnumerable.succ?` will never return `none`.
In other words, it ensures that there will always be a successor.
-/
class InfinitelyUpwardEnumerable (α : Type u) [UpwardEnumerable α] where
  isSome_succ? : ∀ a : α, (UpwardEnumerable.succ? a).isSome

/--
This propositional typeclass ensures that `UpwardEnumerable.succ?` is injective.
-/
class LinearlyUpwardEnumerable (α : Type u) [UpwardEnumerable α] where
  eq_of_succ?_eq : ∀ a b : α, UpwardEnumerable.succ? a = UpwardEnumerable.succ? b → a = b

theorem UpwardEnumerable.isSome_succ? {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] {a : α} :
    (succ? a).isSome :=
  InfinitelyUpwardEnumerable.isSome_succ? a

theorem UpwardEnumerable.eq_of_succ?_eq {α : Type u} [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] {a b : α} (h : succ? a = succ? b) :
    a = b :=
  LinearlyUpwardEnumerable.eq_of_succ?_eq a b h

@[always_inline, inline]
abbrev UpwardEnumerable.succ {α : Type u} [UpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    (a : α) : α :=
  (succ? a).get isSome_succ?

theorem UpwardEnumerable.succ_eq_get {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] {a : α} :
    succ a = (succ? a).get isSome_succ? :=
  (rfl)

theorem UpwardEnumerable.succ?_eq_some {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] {a : α} :
    succ? a = some (succ a) := by
  simp

theorem UpwardEnumerable.eq_of_succ_eq {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [LinearlyUpwardEnumerable α] {a b : α}
    (h : succ a = succ b) : a = b := by
  rw [succ, succ, ← Option.some.injEq, Option.some_get, Option.some_get] at h
  exact eq_of_succ?_eq h

theorem UpwardEnumerable.succ_eq_succ_iff {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [LinearlyUpwardEnumerable α] {a b : α} :
    succ a = succ b ↔ a = b := by
  constructor
  · apply eq_of_succ_eq
  · exact congrArg succ

theorem UpwardEnumerable.isSome_succMany? {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {n : Nat} {a : α} :
    (succMany? n a).isSome := by
  induction n
  · simp [succMany?_zero]
  · rename_i ih
    simp only [succMany?_succ]
    rw [← Option.some_get ih, Option.bind_some]
    apply InfinitelyUpwardEnumerable.isSome_succ?

@[always_inline, inline]
def UpwardEnumerable.succMany {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    (n : Nat) (a : α) :=
  (succMany? n a).get isSome_succMany?

theorem UpwardEnumerable.succMany_eq_get {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {n : Nat} {a : α} :
    succMany n a = (succMany? n a).get isSome_succMany? :=
  (rfl)

theorem UpwardEnumerable.succMany?_eq_some {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {n : Nat} {a : α} :
    succMany? n a = some (succMany n a) := by
  simp [succMany]

theorem UpwardEnumerable.succMany?_eq_some_iff_succMany {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {n : Nat} {a b : α} :
    succMany? n a = some b ↔ succMany n a = b := by
  simp [succMany?_eq_some]

theorem UpwardEnumerable.succMany_one {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {a : α} :
    succMany 1 a = succ a := by
  simp [succMany, succ, succMany?_one]

theorem UpwardEnumerable.succMany_add {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    {m n : Nat} {a : α} : succMany (m + n) a = succMany n (succMany m a) := by
  simp [succMany, succMany?_add]

theorem UpwardEnumerable.succ_le_succ_iff {α : Type w} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {a b : α} :
    UpwardEnumerable.LE (UpwardEnumerable.succ a) (UpwardEnumerable.succ b) ↔
      UpwardEnumerable.LE a b := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [succ] at hn
    refine ⟨n, ?_⟩
    simp [succMany?_eq_some]
    apply eq_of_succ?_eq
    rw [← Option.bind_some (f := succMany? n), Option.some_get,
      ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, Option.some_get] at hn
    rw [← Option.bind_some (f := succ?), ← succMany?_eq_some, ← succMany?_succ, hn]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [succ_eq_get, succ_eq_get, ← Option.bind_some (f := succMany? n), Option.some_get,
      Option.some_get, ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?,
      succMany?_succ, hn, Option.bind_some]

theorem UpwardEnumerable.succ_lt_succ_iff {α : Type w} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {a b : α} :
    UpwardEnumerable.LT (UpwardEnumerable.succ a) (UpwardEnumerable.succ b) ↔
      UpwardEnumerable.LT a b := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [succ] at hn
    refine ⟨n, ?_⟩
    rw [succMany?_eq_some_iff_succMany]
    apply eq_of_succ?_eq
    rw [← Option.bind_some (f := succMany? _), Option.some_get,
      ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, Option.some_get] at hn
    rw [← Option.bind_some (f := succ?), ← succMany?_eq_some, ← succMany?_succ, hn]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [succ_eq_get, succ_eq_get, ← Option.bind_some (f := succMany? _), Option.some_get,
      Option.some_get, ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?,
      succMany?_succ, hn, Option.bind_some]

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `≤`.
In this case, `UpwardEnumerable α` fully characterizes the `LE α` instance.
-/
class LawfulUpwardEnumerableLE (α : Type u) [UpwardEnumerable α] [LE α] where
  /--
  `a` is less than or equal to `b` if and only if `b` is either `a` or a transitive successor
  of `a`.
  -/
  le_iff (a b : α) : a ≤ b ↔ UpwardEnumerable.LE a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `<`.
In this case, `UpwardEnumerable α` fully characterizes the `LT α` instance.
-/
class LawfulUpwardEnumerableLT (α : Type u) [UpwardEnumerable α] [LT α] where
  /--
  `a` is less than `b` if and only if `b` is a proper transitive successor of `a`.
  -/
  lt_iff (a b : α) : a < b ↔ UpwardEnumerable.LT a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with a `Least? α`
instance. For nonempty `α`, it ensures that `least?` has a value and that every other value is
a transitive successor of it.
-/
class LawfulUpwardEnumerableLeast? (α : Type u) [UpwardEnumerable α] [Least? α] where
  /-- For nonempty `α`, `least?` has a value and every other value is a transitive successor of it. -/
  eq_succMany?_least? (a : α) : ∃ init, Least?.least? = some init ∧ UpwardEnumerable.LE init a

end Std.PRange
