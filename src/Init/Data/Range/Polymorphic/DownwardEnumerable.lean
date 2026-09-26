/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Woosuk Kwak
-/
module

prelude
public import Init.Data.Order.Classes
public import Init.Classical
import Init.Data.Option.Lemmas

public section

namespace Std.PRange

/--
This typeclass provides the function `pred? : α → Option α` that computes the predecessor of
elements of `α`, or none if no predecessor exists.
It also provides the function `predMany?`, which computes `n`-th predecessors.

`pred?` is expected to be acyclic: No element is its own transitive predecessor.
If `α` is ordered, then every element smaller than `a : α` should be a transitive predecessor of
`a`. These properties and the compatibility of `pred?` with `predMany?` are encoded in the
typeclasses `LawfulDownwardEnumerable`, `LawfulDownwardEnumerableLE` and `LawfulUpwardEnumerableLT`.

-/
@[ext]
class DownwardEnumerable (α : Type u) where
  /-- Maps elements of `α` to their predecessor, or none if no predecessor exists. -/
  pred? : α → Option α
  /--
  Maps elements of `α` to their `n`-th predecessor, or none if no predecessor exists.
  This should semantically behave like repeatedly applying `pred?`, but it might be more efficient.

  `LawfulDownwardEnumerable` ensures the compatibility with `pred?`.

  If no other implementation is provided in `DownwardEnumerable` instance, `predMany?` repeatedly
  applies `pred?`.
  -/
  predMany? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= pred?) n (some a)

export DownwardEnumerable (pred? predMany?)

/--
According to `DownwardEnumerable.LE`, `a` is less than or equal to `b` if `a` is `b` or a transitive
predecessor of `b`.
-/
@[expose]
protected def DownwardEnumerable.LE {α : Type u} [DownwardEnumerable α] (a b : α) : Prop :=
  ∃ n, predMany? n b = some a

protected theorem DownwardEnumerable.le_iff_exists {α : Type u} {_ : DownwardEnumerable α} {a b : α} :
    DownwardEnumerable.LE a b ↔ ∃ n, predMany? n b = some a :=
  Iff.rfl

/--
According to `DownwardEnumerable.LT`, `a` is less than `b` if `a` is a proper transitive
predecessor of `b`. 'Proper' means that `a` is the `n`-th predecessor of `b`, where `n > 0`.

Given `LawfulDownwardEnumerable α`, no element of `α` is less than itself.
-/
@[expose]
protected def DownwardEnumerable.LT {α : Type u} [DownwardEnumerable α] (a b : α) : Prop :=
  ∃ n, predMany? (n + 1) b = some a

protected theorem DownwardEnumerable.lt_iff_exists {α : Type u} [DownwardEnumerable α] {a b : α} :
    DownwardEnumerable.LT a b ↔ ∃ n, predMany? (n + 1) b = some a :=
  Iff.rfl

protected theorem DownwardEnumerable.le_of_lt {α : Type u} [DownwardEnumerable α] {a b : α}
    (h : DownwardEnumerable.LT a b) : DownwardEnumerable.LE a b :=
  ⟨h.choose + 1, h.choose_spec⟩

/--
The typeclass `Greatest? α` optionally provides a largest element of `α`, `greatest? : Option α`.

The main use case of this typeclass is to use it in combination with `DownwardEnumerable` to
obtain a (possibly infinite) descending enumeration of all elements of `α`.
-/
class Greatest? (α : Type u) where
  /--
  Returns the largest element of `α`, or none if `α` is empty.

  Only empty types are allowed to define `greatest? := none`. If `α` is ordered and nonempty, then
  the value of `greatest?` should be the largest element according to the order on `α`.
  -/
  greatest? : Option α

export Greatest? (greatest?)

/--
This typeclass ensures that an `DownwardEnumerable α` instance is well-behaved.
-/
class LawfulDownwardEnumerable (α : Type u) [DownwardEnumerable α] where
  /-- There is no cyclic chain of predecessors. -/
  ne_of_lt (a b : α) : DownwardEnumerable.LT a b → a ≠ b
  /-- The `0`-th predecessor of `a` is `a` itself. -/
  predMany?_zero (a : α) : predMany? 0 a = some a
  /--
  The `n + 1`-th predecessor of `a` is the predecessor of the `n`-th predecessor, given that said
  predecessors actually exist.
  -/
  predMany?_add_one (n : Nat) (a : α) :
    predMany? (n + 1) a = (predMany? n a).bind pred?

theorem DownwardEnumerable.predMany?_zero [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {a : α} :
    predMany? 0 a = some a :=
  LawfulDownwardEnumerable.predMany?_zero a

theorem DownwardEnumerable.predMany?_add_one [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {n : Nat} {a : α} :
    predMany? (n + 1) a = (predMany? n a).bind pred? :=
  LawfulDownwardEnumerable.predMany?_add_one n a

theorem DownwardEnumerable.predMany?_one [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {a : α} :
    predMany? 1 a = pred? a := by
  simp [predMany?_add_one, predMany?_zero]

theorem DownwardEnumerable.predMany?_add [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {m n : Nat} {a : α} :
    predMany? (m + n) a = (predMany? m a).bind (predMany? n ·) := by
  induction n
  case zero => simp [predMany?_zero]
  case succ n ih =>
    rw [← Nat.add_assoc, predMany?_add_one, ih, Option.bind_assoc]
    simp [predMany?_add_one]

theorem DownwardEnumerable.predMany?_add_one_eq_pred?_bind_predMany?
    [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {n : Nat} {a : α} :
    predMany? (n + 1) a = (pred? a).bind (predMany? n ·) := by
  rw [Nat.add_comm]
  simp [predMany?_add, predMany?_add_one, predMany?_zero]

export DownwardEnumerable (predMany?_zero predMany?_add_one predMany?_one
                           predMany?_add predMany?_add_one_eq_pred?_bind_predMany?)

protected theorem DownwardEnumerable.le_refl {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] (a : α) : DownwardEnumerable.LE a a :=
  ⟨0, predMany?_zero⟩

protected theorem DownwardEnumerable.lt_irrefl {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a : α} : ¬ DownwardEnumerable.LT a a :=
  fun h => LawfulDownwardEnumerable.ne_of_lt a a h rfl

protected theorem DownwardEnumerable.lt_pred? {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} (h : pred? a = some b) : DownwardEnumerable.LT b a :=
  ⟨0, by simpa [DownwardEnumerable.predMany?_one] using h⟩

protected theorem DownwardEnumerable.ne_of_lt {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} (h : DownwardEnumerable.LT a b) : a ≠ b :=
  LawfulDownwardEnumerable.ne_of_lt a b h

protected theorem DownwardEnumerable.le_trans {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b c : α} (hab : DownwardEnumerable.LE a b)
    (hbc : DownwardEnumerable.LE b c) : DownwardEnumerable.LE a c := by
  refine ⟨hbc.choose + hab.choose, ?_⟩
  simp [predMany?_add, hab.choose_spec, hbc.choose_spec]

theorem DownwardEnumerable.le_of_pred?_eq {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} (hab : DownwardEnumerable.pred? a = some b) :
    DownwardEnumerable.LE b a :=
  ⟨1, by simp [predMany?_one, hab]⟩

protected theorem DownwardEnumerable.lt_of_lt_of_le {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b c : α} (hab : DownwardEnumerable.LT a b)
    (hbc : DownwardEnumerable.LE b c) : DownwardEnumerable.LT a c := by
  refine ⟨hbc.choose + hab.choose, ?_⟩
  rw [Nat.add_assoc, predMany?_add, hbc.choose_spec, Option.bind_some, hab.choose_spec]

protected theorem DownwardEnumerable.lt_of_le_of_lt {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b c : α} (hab : DownwardEnumerable.LE a b)
    (hbc : DownwardEnumerable.LT b c) : DownwardEnumerable.LT a c := by
  refine ⟨hbc.choose + hab.choose, ?_⟩
  rw [Nat.add_right_comm, predMany?_add, hbc.choose_spec, Option.bind_some, hab.choose_spec]

protected theorem DownwardEnumerable.lt_trans {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b c : α} (hab : DownwardEnumerable.LT a b)
    (hbc : DownwardEnumerable.LT b c) : DownwardEnumerable.LT a c := by
  refine ⟨(hbc.choose + 1) + hab.choose, ?_⟩
  rw [Nat.add_assoc, predMany?_add, hbc.choose_spec, Option.bind_some, hab.choose_spec]

protected theorem DownwardEnumerable.lt_of_le_of_ne {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} (hle : DownwardEnumerable.LE a b) (hne : a ≠ b) :
    DownwardEnumerable.LT a b := by
  obtain ⟨n, hn⟩ := hle
  match n with
  | 0 => simp [predMany?_zero] at hn; simp [hn] at hne
  | n + 1 => exact ⟨n, hn⟩

protected theorem DownwardEnumerable.not_gt_of_le {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} :
    DownwardEnumerable.LE a b → ¬ DownwardEnumerable.LT b a := by
  rintro ⟨n, hle⟩ ⟨m, hgt⟩
  have : DownwardEnumerable.LT b b := by
    refine ⟨n + m, ?_⟩
    rw [Nat.add_assoc, predMany?_add, hle, Option.bind_some, hgt]
  exact DownwardEnumerable.ne_of_lt this rfl

protected theorem DownwardEnumerable.not_ge_of_lt {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} :
    DownwardEnumerable.LT a b → ¬ DownwardEnumerable.LE b a :=
  flip DownwardEnumerable.not_gt_of_le

protected theorem DownwardEnumerable.not_gt_of_lt {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} (h : DownwardEnumerable.LT a b) :
    ¬ DownwardEnumerable.LT b a :=
  DownwardEnumerable.not_gt_of_le (DownwardEnumerable.le_of_lt h)

instance [DownwardEnumerable α] [LawfulDownwardEnumerable α] : Asymm (α := α) DownwardEnumerable.LT
    where
  asymm _ _ := DownwardEnumerable.not_gt_of_lt

/--
This propositional typeclass ensures that `DownwardEnumerable.pred?` will never return `none`.
In other words, it ensures that there will always be a predecessor.
-/
class InfinitelyDownwardEnumerable (α : Type u) [DownwardEnumerable α] where
  /--
  Every element of `α` has a predecessor.
  -/
  isSome_pred? : ∀ a : α, (DownwardEnumerable.pred? a).isSome

/--
This propositional typeclass ensures that `DownwardEnumerable.pred?` is injective.
-/
class LinearlyDownwardEnumerable (α : Type u) [DownwardEnumerable α] where
  /-- The implementation of `DownwardEnumerable.pred?` for `α` is injective. -/
  eq_of_pred?_eq : ∀ a b : α, DownwardEnumerable.pred? a = DownwardEnumerable.pred? b → a = b

/--
If a type is infinitely downwardly enumerable, then every element has a predecessor.
-/
theorem DownwardEnumerable.isSome_pred? {α : Type u} [DownwardEnumerable α]
    [InfinitelyDownwardEnumerable α] {a : α} : (pred? a).isSome :=
  InfinitelyDownwardEnumerable.isSome_pred? a

theorem DownwardEnumerable.pred?_inj {α : Type u} [DownwardEnumerable α]
    [LinearlyDownwardEnumerable α] {a b : α} :
    pred? a = pred? b ↔ a = b :=
  ⟨LinearlyDownwardEnumerable.eq_of_pred?_eq a b, congrArg pred?⟩

/--
Maps elements of `α` to their immediate predecessor.
-/
@[always_inline, inline]
abbrev DownwardEnumerable.pred {α : Type u} [DownwardEnumerable α] [InfinitelyDownwardEnumerable α]
    (a : α) : α :=
  (pred? a).get isSome_pred?

theorem DownwardEnumerable.pred_eq_get {α : Type u} [DownwardEnumerable α]
    [InfinitelyDownwardEnumerable α] {a : α} :
    pred a = (pred? a).get isSome_pred? :=
  (rfl)

theorem DownwardEnumerable.pred?_eq_some {α : Type u} [DownwardEnumerable α]
    [InfinitelyDownwardEnumerable α] {a : α} :
    pred? a = some (pred a) := by
  simp

theorem DownwardEnumerable.pred_inj {α : Type u} [DownwardEnumerable α]
    [InfinitelyDownwardEnumerable α] [LinearlyDownwardEnumerable α] {a b : α} :
    pred a = pred b ↔ a = b := by
  simp [pred, Option.get_inj, pred?_inj]

theorem DownwardEnumerable.pred_eq_pred_iff {α : Type u} [DownwardEnumerable α]
    [InfinitelyDownwardEnumerable α] [LinearlyDownwardEnumerable α] {a b : α} :
    pred a = pred b ↔ a = b := by
  constructor
  · apply pred_inj.mp
  · exact congrArg pred

theorem DownwardEnumerable.isSome_predMany? {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {n : Nat} {a : α} :
    (predMany? n a).isSome := by
  induction n
  · simp [predMany?_zero]
  · rename_i ih
    simp only [predMany?_add_one]
    rw [← Option.some_get ih, Option.bind_some]
    apply InfinitelyDownwardEnumerable.isSome_pred?

/--
Maps elements of `α` to their `n`-th predecessor. This should semantically behave like repeatedly
applying `pred`, but it might be more efficient.

This function uses a `DownwardEnumerable α` instance.
`LawfulDownwardEnumerable α` ensures the compatibility with `pred` and `pred?`.

If no other implementation is provided in DownwardEnumerable instance, predMany? repeatedly applies
pred?.
-/
@[always_inline, inline, expose]
def DownwardEnumerable.predMany {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α]
    (n : Nat) (a : α) :=
  (predMany? n a).get isSome_predMany?

theorem DownwardEnumerable.predMany_eq_get {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {n : Nat} {a : α} :
    predMany n a = (predMany? n a).get isSome_predMany? :=
  (rfl)

theorem DownwardEnumerable.predMany?_eq_some {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {n : Nat} {a : α} :
    predMany? n a = some (predMany n a) := by
  simp [predMany]

theorem DownwardEnumerable.predMany?_eq_some_iff_predMany {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {n : Nat} {a b : α} :
    predMany? n a = some b ↔ predMany n a = b := by
  simp [predMany?_eq_some]

theorem DownwardEnumerable.predMany_zero {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    predMany 0 a = a := by
  simp [predMany, predMany?_zero]

theorem DownwardEnumerable.predMany_one {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    predMany 1 a = pred a := by
  simp [predMany, pred, predMany?_one]

theorem DownwardEnumerable.predMany_pred {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    predMany (n + 1) a = pred (predMany n a) := by
  simp [predMany_eq_get, predMany?_add_one]

theorem DownwardEnumerable.predMany_add_one_eq_predMany_pred {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    predMany (n + 1) a = (predMany n (pred a)) := by
  simp [predMany_eq_get, predMany?_add_one_eq_pred?_bind_predMany?]

theorem DownwardEnumerable.predMany_pred_eq_pred_predMany {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    predMany n (pred a) = pred (predMany n a) := by
  simp [← predMany_add_one_eq_predMany_pred, predMany_pred]

theorem DownwardEnumerable.predMany_add {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α]
    {m n : Nat} {a : α} : predMany (m + n) a = predMany n (predMany m a) := by
  simp [predMany, predMany?_add]

export DownwardEnumerable (isSome_pred? pred?_inj pred pred_eq_get pred?_eq_some pred_inj
                           pred_eq_pred_iff isSome_predMany? predMany predMany_eq_get
                           predMany?_eq_some predMany?_eq_some_iff_predMany predMany_one
                           predMany_zero predMany_add)

protected theorem DownwardEnumerable.lt_pred {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a : α} :
    DownwardEnumerable.LT (pred a) a := by
  exact DownwardEnumerable.lt_pred? (by simp)

theorem DownwardEnumerable.pred_le_pred {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α]
    {a b : α} (h : DownwardEnumerable.LE a b) : DownwardEnumerable.LE (pred a) (pred b) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [predMany?_eq_some, Option.some_inj] at hn
  rw [predMany?_eq_some, predMany_pred_eq_pred_predMany, hn]

theorem DownwardEnumerable.pred_le_pred_iff {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] [LinearlyDownwardEnumerable α]
    {a b : α} :
    DownwardEnumerable.LE (pred a) (pred b) ↔ DownwardEnumerable.LE a b := by
  refine ⟨fun h => ?_, pred_le_pred⟩
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [predMany?_eq_some_iff_predMany, predMany_pred_eq_pred_predMany, pred_inj] at hn
  rw [predMany?_eq_some_iff_predMany, hn]

theorem DownwardEnumerable.pred_lt_pred {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α]
    {a b : α} (h : DownwardEnumerable.LT a b) : DownwardEnumerable.LT (pred a) (pred b) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [predMany?_eq_some, Option.some_inj] at hn
  rw [predMany?_eq_some, predMany_pred_eq_pred_predMany, hn]

theorem DownwardEnumerable.pred_lt_pred_iff {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] [LinearlyDownwardEnumerable α]
    {a b : α} :
    DownwardEnumerable.LT (pred a) (pred b) ↔ DownwardEnumerable.LT a b := by
  refine ⟨fun h => ?_, pred_lt_pred⟩
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [predMany?_eq_some_iff_predMany, predMany_pred_eq_pred_predMany, pred_inj] at hn
  rw [predMany?_eq_some_iff_predMany, hn]

/--
This typeclass ensures that a `DownwardEnumerable α` instance is compatible with `≤`.
In this case, `DownwardEnumerable α` fully characterizes the `LE α` instance.
-/
class LawfulDownwardEnumerableLE (α : Type u) [DownwardEnumerable α] [LE α] where
  /--
  `a` is less than or equal to `b` if and only if `a` is either `b` or a transitive predecessor
  of `b`.
  -/
  protected le_iff (a b : α) : a ≤ b ↔ DownwardEnumerable.LE a b

protected theorem DownwardEnumerable.le_iff {α : Type u} [LE α] [DownwardEnumerable α]
    [LawfulDownwardEnumerableLE α] {a b : α} : a ≤ b ↔ DownwardEnumerable.LE a b :=
  LawfulDownwardEnumerableLE.le_iff a b

@[expose, instance_reducible]
def DownwardEnumerable.instLETransOfLawfulDownwardEnumerableLE {α : Type u} [LE α]
    [DownwardEnumerable α] [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α] :
    Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := by simpa [DownwardEnumerable.le_iff] using @DownwardEnumerable.le_trans

/--
This typeclass ensures that a `DownwardEnumerable α` instance is compatible with `<`.
In this case, `DownwardEnumerable α` fully characterizes the `LT α` instance.
-/
class LawfulDownwardEnumerableLT (α : Type u) [DownwardEnumerable α] [LT α] where
  /--
  `a` is less than `b` if and only if `a` is a proper transitive predecessor of `b`.
  -/
  lt_iff (a b : α) : a < b ↔ DownwardEnumerable.LT a b

protected theorem DownwardEnumerable.lt_iff {α : Type u} [LT α] [DownwardEnumerable α]
    [LawfulDownwardEnumerableLT α] {a b : α} : a < b ↔ DownwardEnumerable.LT a b :=
  LawfulDownwardEnumerableLT.lt_iff a b

protected theorem DownwardEnumerable.le_iff_lt_or_eq {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] {a b : α} :
    DownwardEnumerable.LE a b ↔ DownwardEnumerable.LT a b ∨ a = b := by
  apply Iff.intro
  · rintro ⟨n, hn⟩
    match n with
    | 0 => exact Or.inr (by simp [DownwardEnumerable.predMany?_zero] at hn; rw [hn])
    | n + 1 => exact Or.inl ⟨_, hn⟩
  · intro h
    open Classical in
    match heq : decide (a = b) with
    | true =>
      simp only [decide_eq_true_eq] at heq
      exact heq ▸ DownwardEnumerable.le_refl _
    | false =>
      simp only [decide_eq_false_iff_not] at heq
      simp only [heq, or_false] at h
      exact DownwardEnumerable.le_of_lt h

protected theorem DownwardEnumerable.le_pred_iff {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] {a b : α} :
    DownwardEnumerable.LE a (pred b) ↔ DownwardEnumerable.LT a b := by
  constructor
  · rintro ⟨n, hn⟩
    rw [predMany?_eq_some_iff_predMany, ← predMany_add_one_eq_predMany_pred,
      ← predMany?_eq_some_iff_predMany] at hn
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    rw [predMany?_eq_some_iff_predMany, predMany_add_one_eq_predMany_pred,
      ← predMany?_eq_some_iff_predMany] at hn
    exact ⟨n, hn⟩

protected theorem DownwardEnumerable.pred_lt_iff {α : Type u} [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [InfinitelyDownwardEnumerable α] [LinearlyDownwardEnumerable α]
    {a b : α} : DownwardEnumerable.LT (pred a) b ↔ DownwardEnumerable.LE a b := by
  constructor
  · rintro ⟨n, hn⟩
    rw [predMany?_eq_some_iff_predMany, predMany_pred, pred_inj,
      ← predMany?_eq_some_iff_predMany] at hn
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    rw [predMany?_eq_some_iff_predMany, ← pred_inj, ← predMany_pred,
      ← predMany?_eq_some_iff_predMany] at hn
    exact ⟨n, hn⟩

@[expose, instance_reducible]
def DownwardEnumerable.instLTTransOfLawfulDownwardEnumerableLT {α : Type u} [LT α]
    [DownwardEnumerable α] [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α] :
    Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans := by simpa [DownwardEnumerable.lt_iff] using @DownwardEnumerable.lt_trans

theorem DownwardEnumerable.instLawfulOrderLTOfLawfulDownwardEnumerableLT {α : Type u} [LT α] [LE α]
    [DownwardEnumerable α] [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    [LawfulDownwardEnumerableLE α] :
    LawfulOrderLT α where
  lt_iff a b := by
    simp [DownwardEnumerable.lt_iff, DownwardEnumerable.le_iff]
    constructor
    · intro h
      exact ⟨DownwardEnumerable.le_of_lt h, DownwardEnumerable.not_ge_of_lt h⟩
    · intro h
      exact DownwardEnumerable.lt_of_le_of_ne h.1 (h.2.imp (· ▸ DownwardEnumerable.le_refl b))

/--
This typeclass ensures that a `DownwardEnumerable α` instance is compatible with a `Greatest? α`
instance. For nonempty `α`, it ensures that `greatest?` has a value and that every other value is
a transitive predecessor of it.
-/
class LawfulDownwardEnumerableGreatest? (α : Type u) [DownwardEnumerable α] [Greatest? α] where
  /--
  For nonempty `α`, `greatest?` has a value and every other value is a transitive predecessor of it.
  -/
  le_greatest? (a : α) : ∃ init, Greatest?.greatest? = some init ∧ DownwardEnumerable.LE a init

theorem DownwardEnumerable.le_greatest? {α : Type u} [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] {a : α} :
    ∃ init, greatest? = some init ∧ DownwardEnumerable.LE a init :=
  LawfulDownwardEnumerableGreatest?.le_greatest? a

theorem DownwardEnumerable.isSome_greatest? {α : Type u} [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] [hn : Nonempty α] :
    (greatest? (α := α)).isSome := by
  obtain ⟨_, h, _⟩ := le_greatest? (α := α) (a := Classical.ofNonempty)
  simp [h]

def DownwardEnumerable.greatest [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] [hn : Nonempty α] : α :=
  greatest?.get isSome_greatest?

theorem DownwardEnumerable.le_greatest [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] {a : α} :
    DownwardEnumerable.LE a (greatest (hn := ⟨a⟩)) := by
  obtain ⟨_, h, _⟩ := le_greatest? (a := a)
  simp [greatest, *]

theorem DownwardEnumerable.greatest?_eq_some {α : Type u} [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] [hn : Nonempty α] :
    greatest? (α := α) = some greatest := by
  simp [greatest]

theorem DownwardEnumerable.isSome_greatest?_iff {α : Type u} [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] :
    (greatest? (α := α)).isSome ↔ Nonempty α := by
  constructor
  · simp only [Option.isSome_iff_exists]
    rintro ⟨a, _⟩
    exact ⟨a⟩
  · rintro ⟨a⟩
    obtain ⟨_, h, _⟩ := LawfulDownwardEnumerableGreatest?.le_greatest? (a := a)
    simp [h]

theorem DownwardEnumerable.greatest?_eq_none_iff {α : Type u} [DownwardEnumerable α] [Greatest? α]
    [LawfulDownwardEnumerableGreatest? α] :
    greatest? (α := α) = none ↔ ¬ Nonempty α := by
  simp [← isSome_greatest?_iff]

end Std.PRange
