/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Classical
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Option.Lemmas
import Init.NotationExtra

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
According to `UpwardEnumerable.le`, `a` is less than or equal to `b` if `b` is `a` or a transitive
successor of `a`.
-/
@[expose]
def UpwardEnumerable.le {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? n a = some b

/--
According to `UpwardEnumerable.lt`, `a` is less than `b` if `b` is a proper transitive successor of
`a`. 'Proper' means that `b` is the `n`-th successor of `a`, where `n > 0`.

Given `LawfulUpwardEnumerable α`, no element of `α` is less than itself.
-/
@[expose]
def UpwardEnumerable.lt {α : Type u} [UpwardEnumerable α] (a b : α) : Prop :=
  ∃ n, UpwardEnumerable.succMany? (n + 1) a = some b

theorem UpwardEnumerable.le_of_lt {α : Type u} [UpwardEnumerable α] {a b : α}
    (h : UpwardEnumerable.lt a b) : UpwardEnumerable.le a b :=
  ⟨h.choose + 1, h.choose_spec⟩

/--
The typeclass `Least? α` optionally provides a smallest element of `α`, `least? : Option α`.

The main use case of this typeclass is to use it in combination with `UpwardEnumerable` to
obtain a (possibly infinite) ascending enumeration of all elements of `α`.
-/
class Least? (α : Type u) extends UpwardEnumerable α where
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
  ne_of_lt (a b : α) : UpwardEnumerable.lt a b → a ≠ b
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

theorem UpwardEnumerable.succMany?_add [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (m n : Nat) (a : α) :
    UpwardEnumerable.succMany? (m + n) a =
      (UpwardEnumerable.succMany? m a).bind (UpwardEnumerable.succMany? n ·) := by
  induction n
  case zero => simp [LawfulUpwardEnumerable.succMany?_zero]
  case succ n ih=>
    rw [← Nat.add_assoc, LawfulUpwardEnumerable.succMany?_succ, ih, Option.bind_assoc]
    simp only [LawfulUpwardEnumerable.succMany?_succ]

theorem LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (n : Nat) (a : α) :
    UpwardEnumerable.succMany? (n + 1) a =
      (UpwardEnumerable.succ? a).bind (UpwardEnumerable.succMany? n ·) := by
  rw [Nat.add_comm]
  simp [UpwardEnumerable.succMany?_add, LawfulUpwardEnumerable.succMany?_succ,
    LawfulUpwardEnumerable.succMany?_zero]

theorem UpwardEnumerable.le_refl {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (a : α) : UpwardEnumerable.le a a :=
  ⟨0, LawfulUpwardEnumerable.succMany?_zero a⟩

theorem UpwardEnumerable.le_trans {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b c : α} (hab : UpwardEnumerable.le a b) (hbc : UpwardEnumerable.le b c) :
    UpwardEnumerable.le a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  simp [succMany?_add, hab.choose_spec, hbc.choose_spec]

theorem UpwardEnumerable.lt_of_lt_of_le {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b c : α} (hab : UpwardEnumerable.lt a b) (hbc : UpwardEnumerable.le b c) :
    UpwardEnumerable.lt a c := by
  refine ⟨hab.choose + hbc.choose, ?_⟩
  rw [Nat.add_right_comm, succMany?_add, hab.choose_spec, Option.bind_some, hbc.choose_spec]

theorem UpwardEnumerable.not_gt_of_le {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.le a b → ¬ UpwardEnumerable.lt b a := by
  rintro ⟨n, hle⟩ ⟨m, hgt⟩
  have : UpwardEnumerable.lt a a := by
    refine ⟨n + m, ?_⟩
    rw [Nat.add_assoc, UpwardEnumerable.succMany?_add, hle, Option.bind_some, hgt]
  exact LawfulUpwardEnumerable.ne_of_lt _ _ this rfl

theorem UpwardEnumerable.ne_of_lt {α : Type w} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {a b : α} :
    UpwardEnumerable.lt a b → a ≠ b :=
  LawfulUpwardEnumerable.ne_of_lt a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `≤`.
In this case, `UpwardEnumerable α` fully characterizes the `LE α` instance.
-/
class LawfulUpwardEnumerableLE (α : Type u) [UpwardEnumerable α] [LE α] where
  /--
  `a` is less than or equal to `b` if and only if `b` is either `a` or a transitive successor
  of `a`.
  -/
  le_iff (a b : α) : a ≤ b ↔ UpwardEnumerable.le a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with `<`.
In this case, `UpwardEnumerable α` fully characterizes the `LT α` instance.
-/
class LawfulUpwardEnumerableLT (α : Type u) [UpwardEnumerable α] [LT α] where
  /--
  `a` is less than `b` if and only if `b` is a proper transitive successor of `a`.
  -/
  lt_iff (a b : α) : a < b ↔ UpwardEnumerable.lt a b

/--
This typeclass ensures that an `UpwardEnumerable α` instance is compatible with a `Least? α`
instance. For nonempty `α`, it ensures that `least?` has a value and that every other value is
a transitive successor of it.
-/
class LawfulUpwardEnumerableLeast? (α : Type u) [UpwardEnumerable α] [Least? α] where
  /--For nonempty `α`, `least?` has a value and every other value is a transitive successor of it. -/
  eq_succMany?_least? (a : α) : ∃ init, Least?.least? = some init ∧ UpwardEnumerable.le init a

end Std.PRange
