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

attribute [simp] UpwardEnumerable.succ? UpwardEnumerable.succMany?
export UpwardEnumerable (succ? succMany?)

/--
According to `UpwardEnumerable.LE`, `a` is less than or equal to `b` if `b` is `a` or a transitive
successor of `a`.
-/
@[expose]
protected def UpwardEnumerable.LE {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, succMany? n a = some b

/--
According to `UpwardEnumerable.LT`, `a` is less than `b` if `b` is a proper transitive successor of
`a`. 'Proper' means that `b` is the `n`-th successor of `a`, where `n > 0`.

Given `LawfulUpwardEnumerable α`, no element of `α` is less than itself.
-/
@[expose]
protected def UpwardEnumerable.LT {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, succMany? (n + 1) a = some b

protected theorem UpwardEnumerable.le_of_lt {α : Type u} [UpwardEnumerable α] {a b : α}
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

attribute [simp] Least?.least?
export Least? (least?)

/--
This typeclass ensures that an `UpwardEnumerable α` instance is well-behaved.
-/
class LawfulUpwardEnumerable (α : Type u) [UpwardEnumerable α] where
  /-- There is no cyclic chain of successors. -/
  ne_of_lt (a b : α) : UpwardEnumerable.LT a b → a ≠ b
  /-- The `0`-th successor of `a` is `a` itself. -/
  succMany?_zero (a : α) : succMany? 0 a = some a
  /--
  The `n + 1`-th successor of `a` is the successor of the `n`-th successor, given that said
  successors actually exist.
  -/
  succMany?_succ (n : Nat) (a : α) :
    succMany? (n + 1) a = (succMany? n a).bind succ?

theorem UpwardEnumerable.succMany?_zero [UpwardEnumerable α] [LawfulUpwardEnumerable α] {a : α} :
    succMany? 0 a = some a :=
  LawfulUpwardEnumerable.succMany?_zero a

theorem UpwardEnumerable.succMany?_succ? [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Nat} {a : α} :
    succMany? (n + 1) a = (succMany? n a).bind succ? :=
  LawfulUpwardEnumerable.succMany?_succ n a

@[deprecated succMany?_succ? (since := "2025-09-03")]
theorem UpwardEnumerable.succMany?_succ [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Nat} {a : α} :
    succMany? (n + 1) a = (succMany? n a).bind succ? :=
  succMany?_succ?

theorem UpwardEnumerable.succMany?_one [UpwardEnumerable α] [LawfulUpwardEnumerable α] {a : α} :
    succMany? 1 a = succ? a := by
  simp [succMany?_succ?, succMany?_zero]

theorem UpwardEnumerable.succMany?_add [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {m n : Nat} {a : α} :
    succMany? (m + n) a = (succMany? m a).bind (succMany? n ·) := by
  induction n
  case zero => simp [succMany?_zero]
  case succ n ih =>
    rw [← Nat.add_assoc, succMany?_succ?, ih, Option.bind_assoc]
    simp [succMany?_succ?]

theorem UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Nat} {a : α} :
    succMany? (n + 1) a = (succ? a).bind (succMany? n ·) := by
  rw [Nat.add_comm]
  simp [succMany?_add, succMany?_succ?, succMany?_zero]

@[deprecated UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany? (since := "2025-09-03")]
theorem LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (n : Nat) (a : α) :
    succMany? (n + 1) a = (succ? a).bind (succMany? n ·) :=
  UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?

export UpwardEnumerable (succMany?_zero succMany?_succ? succMany?_one succMany?_add
                         succMany?_succ?_eq_succ?_bind_succMany?)

protected theorem UpwardEnumerable.le_refl {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] (a : α) : UpwardEnumerable.LE a a :=
  ⟨0, succMany?_zero⟩

protected theorem UpwardEnumerable.lt_irrefl {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a : α} : ¬ UpwardEnumerable.LT a a :=
  fun h => LawfulUpwardEnumerable.ne_of_lt a a h rfl

protected theorem UpwardEnumerable.ne_of_lt {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b : α} (h : UpwardEnumerable.LT a b) : a ≠ b :=
  LawfulUpwardEnumerable.ne_of_lt a b h

protected theorem UpwardEnumerable.le_trans {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b c : α} (hab : UpwardEnumerable.LE a b)
    (hbc : UpwardEnumerable.LE b c) : UpwardEnumerable.LE a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  simp [succMany?_add, hab.choose_spec, hbc.choose_spec]

theorem UpwardEnumerable.le_of_succ?_eq {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} (hab : UpwardEnumerable.succ? a = some b) : UpwardEnumerable.LE a b :=
  ⟨1, by simp [succMany?_one, hab]⟩

protected theorem UpwardEnumerable.lt_of_lt_of_le {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b c : α} (hab : UpwardEnumerable.LT a b)
    (hbc : UpwardEnumerable.LE b c) : UpwardEnumerable.LT a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  rw [Nat.add_right_comm, succMany?_add, hab.choose_spec, Option.bind_some, hbc.choose_spec]

protected theorem UpwardEnumerable.lt_of_le_of_lt {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b c : α} (hab : UpwardEnumerable.LE a b)
    (hbc : UpwardEnumerable.LT b c) : UpwardEnumerable.LT a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  rw [Nat.add_assoc, succMany?_add, hab.choose_spec, Option.bind_some, hbc.choose_spec]

protected theorem UpwardEnumerable.not_gt_of_le {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b : α} :
    UpwardEnumerable.LE a b → ¬ UpwardEnumerable.LT b a := by
  rintro ⟨n, hle⟩ ⟨m, hgt⟩
  have : UpwardEnumerable.LT a a := by
    refine ⟨n + m, ?_⟩
    rw [Nat.add_assoc, succMany?_add, hle, Option.bind_some, hgt]
  exact UpwardEnumerable.ne_of_lt this rfl

protected theorem UpwardEnumerable.not_ge_of_lt {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b : α} :
    UpwardEnumerable.LT a b → ¬ UpwardEnumerable.LE b a :=
  flip UpwardEnumerable.not_gt_of_le

protected theorem UpwardEnumerable.not_gt_of_lt {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {a b : α} (h : UpwardEnumerable.LT a b) : ¬ UpwardEnumerable.LT b a :=
  UpwardEnumerable.not_gt_of_le (UpwardEnumerable.le_of_lt h)

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
    [InfinitelyUpwardEnumerable α] {a : α} : (succ? a).isSome :=
  InfinitelyUpwardEnumerable.isSome_succ? a

theorem UpwardEnumerable.succ?_inj {α : Type u} [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    {a b : α} (h : succ? a = succ? b) :
    a = b :=
  LinearlyUpwardEnumerable.eq_of_succ?_eq a b h

@[deprecated succ?_inj (since := "2025-09-03")]
theorem UpwardEnumerable.eq_of_succ?_eq {α : Type u} [UpwardEnumerable α] [LinearlyUpwardEnumerable α]
    {a b : α} (h : succ? a = succ? b) :
    a = b :=
  succ?_inj h

/--
Maps elements of `α` to their immediate successor.
-/
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

theorem UpwardEnumerable.succ_inj {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [LinearlyUpwardEnumerable α] {a b : α}
    (h : succ a = succ b) : a = b := by
  rw [succ, succ, ← Option.some.injEq, Option.some_get, Option.some_get] at h
  exact succ?_inj h

@[deprecated succ_inj (since := "2025-09-03")]
theorem UpwardEnumerable.eq_of_succ_eq {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [LinearlyUpwardEnumerable α] {a b : α}
    (h : succ a = succ b) : a = b :=
  succ_inj h

theorem UpwardEnumerable.succ_eq_succ_iff {α : Type u} [UpwardEnumerable α]
    [InfinitelyUpwardEnumerable α] [LinearlyUpwardEnumerable α] {a b : α} :
    succ a = succ b ↔ a = b := by
  constructor
  · apply succ_inj
  · exact congrArg succ

theorem UpwardEnumerable.isSome_succMany? {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {n : Nat} {a : α} :
    (succMany? n a).isSome := by
  induction n
  · simp [succMany?_zero]
  · rename_i ih
    simp only [succMany?_succ?]
    rw [← Option.some_get ih, Option.bind_some]
    apply InfinitelyUpwardEnumerable.isSome_succ?

/--
Maps elements of `α` to their `n`-th successor. This should semantically behave like repeatedly
applying `succ`, but it might be more efficient.

This function uses an `UpwardEnumerable α` instance.
`LawfulUpwardEnumerable α` ensures the compatibility with `succ` and `succ?`.

If no other implementation is provided in UpwardEnumerable instance, succMany? repeatedly applies succ?.
-/
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

theorem UpwardEnumerable.succMany_zero {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {a : α} :
    succMany 0 a = a := by
  simp [succMany, succMany?_zero]

theorem UpwardEnumerable.succMany_one {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α] {a : α} :
    succMany 1 a = succ a := by
  simp [succMany, succ, succMany?_one]

theorem UpwardEnumerable.succMany_add {α : Type u} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    {m n : Nat} {a : α} : succMany (m + n) a = succMany n (succMany m a) := by
  simp [succMany, succMany?_add]

export UpwardEnumerable (isSome_succ? succ?_inj succ succ_eq_get succ?_eq_some succ_inj
                         succ_eq_succ_iff isSome_succMany? succMany succMany_eq_get
                         succMany?_eq_some succMany?_eq_some_iff_succMany succMany_one succMany_zero
                         succMany_add)

theorem UpwardEnumerable.succ_le_succ_iff {α : Type w} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    {a b : α} : UpwardEnumerable.LE (succ a) (succ b) ↔
      UpwardEnumerable.LE a b := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [succ] at hn
    refine ⟨n, ?_⟩
    simp [succMany?_eq_some]
    apply succ?_inj
    rw [← Option.bind_some (f := succMany? n), Option.some_get,
      ← succMany?_succ?_eq_succ?_bind_succMany?, Option.some_get] at hn
    rw [← Option.bind_some (f := succ?), ← succMany?_eq_some, ← succMany?_succ?, hn]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [succ_eq_get, succ_eq_get, ← Option.bind_some (f := succMany? n), Option.some_get,
      Option.some_get, ← succMany?_succ?_eq_succ?_bind_succMany?,
      succMany?_succ?, hn, Option.bind_some]

theorem UpwardEnumerable.succ_lt_succ_iff {α : Type w} [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.LT (succ a) (succ b) ↔
      UpwardEnumerable.LT a b := by
  constructor
  · rintro ⟨n, hn⟩
    simp only [succ] at hn
    refine ⟨n, ?_⟩
    rw [succMany?_eq_some_iff_succMany]
    apply succ?_inj
    rw [← Option.bind_some (f := succMany? _), Option.some_get,
      ← succMany?_succ?_eq_succ?_bind_succMany?, Option.some_get] at hn
    rw [← Option.bind_some (f := succ?), ← succMany?_eq_some, ← succMany?_succ?, hn]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [succ_eq_get, succ_eq_get, ← Option.bind_some (f := succMany? _), Option.some_get,
      Option.some_get, ← succMany?_succ?_eq_succ?_bind_succMany?, succMany?_succ?, hn,
      Option.bind_some]

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `≤`.
In this case, `UpwardEnumerable α` fully characterizes the `LE α` instance.
-/
class LawfulUpwardEnumerableLE (α : Type u) [UpwardEnumerable α] [LE α] where
  /--
  `a` is less than or equal to `b` if and only if `b` is either `a` or a transitive successor
  of `a`.
  -/
  protected le_iff (a b : α) : a ≤ b ↔ UpwardEnumerable.LE a b

protected theorem UpwardEnumerable.le_iff {α : Type u} [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] {a b : α} : a ≤ b ↔ UpwardEnumerable.LE a b :=
  LawfulUpwardEnumerableLE.le_iff a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `<`.
In this case, `UpwardEnumerable α` fully characterizes the `LT α` instance.
-/
class LawfulUpwardEnumerableLT (α : Type u) [UpwardEnumerable α] [LT α] where
  /--
  `a` is less than `b` if and only if `b` is a proper transitive successor of `a`.
  -/
  lt_iff (a b : α) : a < b ↔ UpwardEnumerable.LT a b

protected theorem UpwardEnumerable.lt_iff {α : Type u} [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] {a b : α} : a < b ↔ UpwardEnumerable.LT a b :=
  LawfulUpwardEnumerableLT.lt_iff a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with a `Least? α`
instance. For nonempty `α`, it ensures that `least?` has a value and that every other value is
a transitive successor of it.
-/
class LawfulUpwardEnumerableLeast? (α : Type u) [UpwardEnumerable α] [Least? α] where
  /-- For nonempty `α`, `least?` has a value and every other value is a transitive successor of it. -/
  least?_le (a : α) : ∃ init, Least?.least? = some init ∧ UpwardEnumerable.LE init a

theorem UpwardEnumerable.least?_le {α : Type u} [UpwardEnumerable α] [Least? α]
    [LawfulUpwardEnumerableLeast? α] {a : α} :
    ∃ init, least? = some init ∧ UpwardEnumerable.LE init a :=
  LawfulUpwardEnumerableLeast?.least?_le a

end Std.PRange
