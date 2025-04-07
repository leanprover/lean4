/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
prelude
import Init.Data.Nat.Bitwise.Basic

open Nat

namespace Fin

instance coeToNat : CoeOut (Fin n) Nat :=
  ⟨fun v => v.val⟩

/--
The type `Fin 0` is uninhabited, so it can be used to derive any result whatsoever.

This is similar to `Empty.elim`. It can be thought of as a compiler-checked assertion that a code
path is unreachable, or a logical contradiction from which `False` and thus anything else could be
derived.
-/
def elim0.{u} {α : Sort u} : Fin 0 → α
  | ⟨_, h⟩ => absurd h (not_lt_zero _)

/--
The successor, with an increased bound.

This differs from adding `1`, which instead wraps around.

Examples:
 * `(2 : Fin 3).succ = (3 : Fin 4)`
 * `(2 : Fin 3) + 1 = (0 : Fin 3)`
-/
def succ : Fin n → Fin (n + 1)
  | ⟨i, h⟩ => ⟨i+1, Nat.succ_lt_succ h⟩

variable {n : Nat}

/--
Returns `a` modulo `n` as a `Fin n`.

The assumption `NeZero n` ensures that `Fin n` is nonempty.
-/
protected def ofNat' (n : Nat) [NeZero n] (a : Nat) : Fin n :=
  ⟨a % n, Nat.mod_lt _ (pos_of_neZero n)⟩

/--
Returns `a` modulo `n + 1` as a `Fin n.succ`.
-/
@[deprecated Fin.ofNat' (since := "2024-11-27")]
protected def ofNat {n : Nat} (a : Nat) : Fin (n + 1) :=
  ⟨a % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

-- We provide this because other similar types have a `toNat` function, but `simp` rewrites
-- `i.toNat` to `i.val`.
/--
Extracts the underlying `Nat` value.

This function is a synonym for `Fin.val`, which is the simp normal form. `Fin.val` is also a
coercion, so values of type `Fin n` are automatically converted to `Nat`s as needed.
-/
@[inline]
protected def toNat (i : Fin n) : Nat :=
  i.val

@[simp] theorem toNat_eq_val {i : Fin n} : i.toNat = i.val := rfl

private theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
  | 0,   h => Nat.mod_lt _ h
  | _+1, h =>
    have : n > 0 := Nat.lt_trans (Nat.zero_lt_succ _) h;
    Nat.mod_lt _ this

/--
Addition modulo `n`, usually invoked via the `+` operator.

Examples:
 * `(2 : Fin 8) + (2 : Fin 8) = (4 : Fin 8)`
 * `(2 : Fin 3) + (2 : Fin 3) = (1 : Fin 3)`
-/
protected def add : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

/--
Multiplication modulo `n`, usually invoked via the `*` operator.

Examples:
 * `(2 : Fin 10) * (2 : Fin 10) = (4 : Fin 10)`
 * `(2 : Fin 10) * (7 : Fin 10) = (4 : Fin 10)`
 * `(3 : Fin 10) * (7 : Fin 10) = (1 : Fin 10)`
-/
protected def mul : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a * b) % n, mlt h⟩

/--
Subtraction modulo `n`, usually invoked via the `-` operator.

Examples:
 * `(5 : Fin 11) - (3 : Fin 11) = (2 : Fin 11)`
 * `(3 : Fin 11) - (5 : Fin 11) = (9 : Fin 11)`
-/
protected def sub : Fin n → Fin n → Fin n
  /-
  The definition of `Fin.sub` has been updated to improve performance.
  The right-hand-side of the following `match` was originally
  ```
  ⟨(a + (n - b)) % n, mlt h⟩
  ```
  This caused significant performance issues when testing definitional equality,
  such as `x =?= x - 1` where `x : Fin n` and `n` is a big number,
  as Lean spent a long time reducing
  ```
  ((n - 1) + x.val) % n
  ```
  For example, this was an issue for `Fin 2^64` (i.e., `UInt64`).
  This change improves performance by leveraging the fact that `Nat.add` is defined
  using recursion on the second argument.
  See issue #4413.
  -/
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨((n - b) + a) % n, mlt h⟩

/-!
Remark: land/lor can be defined without using (% n), but
we are trying to minimize the number of Nat theorems
needed to bootstrap Lean.
-/

/--
Modulus of bounded numbers, usually invoked via the `%` operator.

The resulting value is that computed by the `%` operator on `Nat`.
-/
protected def mod : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a % b,  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

/--
Division of bounded numbers, usually invoked via the `/` operator.

The resulting value is that computed by the `/` operator on `Nat`. In particular, the result of
division by `0` is `0`.

Examples:
 * `(5 : Fin 10) / (2 : Fin 10) = (2 : Fin 10)`
 * `(5 : Fin 10) / (0 : Fin 10) = (0 : Fin 10)`
 * `(5 : Fin 10) / (7 : Fin 10) = (0 : Fin 10)`
-/
protected def div : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h⟩

/--
Modulus of bounded numbers with respect to a `Nat`.

The resulting value is that computed by the `%` operator on `Nat`.
-/
def modn : Fin n → Nat → Fin n
  | ⟨a, h⟩, m => ⟨a % m, Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

/--
Bitwise and.
-/
def land : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.land a b) % n, mlt h⟩

/--
Bitwise or.
-/
def lor : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.lor a b) % n, mlt h⟩

/--
Bitwise xor (“exclusive or”).
-/
def xor : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.xor a b) % n, mlt h⟩

/--
Bitwise left shift of bounded numbers, with wraparound on overflow.

Examples:
 * `(1 : Fin 10) <<< (1 : Fin 10) = (2 : Fin 10)`
 * `(1 : Fin 10) <<< (3 : Fin 10) = (8 : Fin 10)`
 * `(1 : Fin 10) <<< (4 : Fin 10) = (6 : Fin 10)`
-/
def shiftLeft : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a <<< b) % n, mlt h⟩

/--
Bitwise right shift of bounded numbers.

This operator corresponds to logical rather than arithmetic bit shifting. The new bits are always
`0`.

Examples:
 * `(15 : Fin 16) >>> (1 : Fin 16) = (7 : Fin 16)`
 * `(15 : Fin 16) >>> (2 : Fin 16) = (3 : Fin 16)`
 * `(15 : Fin 17) >>> (2 : Fin 17) = (3 : Fin 17)`
-/
def shiftRight : Fin n → Fin n → Fin n
  | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a >>> b) % n, mlt h⟩

instance : Add (Fin n) where
  add := Fin.add

instance : Sub (Fin n) where
  sub := Fin.sub

instance : Mul (Fin n) where
  mul := Fin.mul

instance : Mod (Fin n) where
  mod := Fin.mod

instance : Div (Fin n) where
  div := Fin.div

instance : AndOp (Fin n) where
  and := Fin.land
instance : OrOp (Fin n) where
  or := Fin.lor
instance : Xor (Fin n) where
  xor := Fin.xor
instance : ShiftLeft (Fin n) where
  shiftLeft := Fin.shiftLeft
instance : ShiftRight (Fin n) where
  shiftRight := Fin.shiftRight

instance instOfNat {n : Nat} [NeZero n] {i : Nat} : OfNat (Fin n) i where
  ofNat := Fin.ofNat' n i

instance instInhabited {n : Nat} [NeZero n] : Inhabited (Fin n) where
  default := 0

@[simp] theorem zero_eta : (⟨0, Nat.zero_lt_succ _⟩ : Fin (n + 1)) = 0 := rfl

theorem ne_of_val_ne {i j : Fin n} (h : val i ≠ val j) : i ≠ j :=
  fun h' => absurd (val_eq_of_eq h') h

theorem val_ne_of_ne {i j : Fin n} (h : i ≠ j) : val i ≠ val j :=
  fun h' => absurd (eq_of_val_eq h') h

theorem modn_lt : ∀ {m : Nat} (i : Fin n), m > 0 → (modn i m).val < m
  | _, ⟨_, _⟩, hp =>  by simp [modn]; apply Nat.mod_lt; assumption

theorem val_lt_of_le (i : Fin b) (h : b ≤ n) : i.val < n :=
  Nat.lt_of_lt_of_le i.isLt h

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
protected theorem pos (i : Fin n) : 0 < n :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) i.2

/--
The greatest value of `Fin (n+1)`, namely `n`.

Examples:
 * `Fin.last 4 = (4 : Fin 5)`
 * `(Fin.last 0).val = (0 : Nat)`
-/
@[inline] def last (n : Nat) : Fin (n + 1) := ⟨n, n.lt_succ_self⟩

/--
Replaces the bound with another that is suitable for the value.

The proof embedded in `i` can be used to cast to a larger bound even if the concrete value is not
known.

Examples:
```lean example
example : Fin 12 := (7 : Fin 10).castLT (by decide : 7 < 12)
```
```lean example
example (i : Fin 10) : Fin 12 :=
  i.castLT <| by
    cases i; simp; omega
```
-/
@[inline] def castLT (i : Fin m) (h : i.1 < n) : Fin n := ⟨i.1, h⟩

/--
Coarsens a bound to one at least as large.

See also `Fin.castAdd` for a version that represents the larger bound with addition rather than an
explicit inequality proof.
-/
@[inline] def castLE (h : n ≤ m) (i : Fin n) : Fin m := ⟨i, Nat.lt_of_lt_of_le i.2 h⟩

/--
Uses a proof that two bounds are equal to allow a value bounded by one to be used with the other.

In other words, when `eq : n = m`, `Fin.cast eq i` converts `i : Fin n` into a `Fin m`.
-/
@[inline] protected def cast (eq : n = m) (i : Fin n) : Fin m := ⟨i, eq ▸ i.2⟩

/--
Coarsens a bound to one at least as large.

See also `Fin.natAdd` and `Fin.addNat` for addition functions that increase the bound, and
`Fin.castLE` for a version that uses an explicit inequality proof.
-/
@[inline] def castAdd (m) : Fin n → Fin (n + m) :=
  castLE <| Nat.le_add_right n m

/--
Coarsens a bound by one.
-/
@[inline] def castSucc : Fin n → Fin (n + 1) := castAdd 1

/--
Adds a natural number to a `Fin`, increasing the bound.

This is a generalization of `Fin.succ`.

`Fin.natAdd` is a version of this function that takes its `Nat` parameter first.

Examples:
 * `Fin.addNat (5 : Fin 8) 3 = (8 : Fin 11)`
 * `Fin.addNat (0 : Fin 8) 1 = (1 : Fin 9)`
 * `Fin.addNat (1 : Fin 8) 2 = (3 : Fin 10)`

-/
def addNat (i : Fin n) (m) : Fin (n + m) := ⟨i + m, Nat.add_lt_add_right i.2 _⟩

/--
Adds a natural number to a `Fin`, increasing the bound.

This is a generalization of `Fin.succ`.

`Fin.addNat` is a version of this function that takes its `Nat` parameter second.

Examples:
 * `Fin.natAdd 3 (5 : Fin 8) = (8 : Fin 11)`
 * `Fin.natAdd 1 (0 : Fin 8) = (1 : Fin 9)`
 * `Fin.natAdd 1 (2 : Fin 8) = (3 : Fin 9)`
-/
def natAdd (n) (i : Fin m) : Fin (n + m) := ⟨n + i, Nat.add_lt_add_left i.2 _⟩

/--
Replaces a value with its difference from the largest value in the type.

Considering the values of `Fin n` as a sequence `0`, `1`, …, `n-2`, `n-1`, `Fin.rev` finds the
corresponding element of the reversed sequence. In other words, it maps `0` to `n-1`, `1` to `n-2`,
..., and `n-1` to `0`.

Examples:
 * `(5 : Fin 6).rev = (0 : Fin 6)`
 * `(0 : Fin 6).rev = (5 : Fin 6)`
 * `(2 : Fin 5).rev = (2 : Fin 5)`
-/
@[inline] def rev (i : Fin n) : Fin n := ⟨n - (i + 1), Nat.sub_lt i.pos (Nat.succ_pos _)⟩

/--
Subtraction of a natural number from a `Fin`, with the bound narrowed.

This is a generalization of `Fin.pred`. It is guaranteed to not underflow or wrap around.

Examples:
 * `(5 : Fin 9).subNat 2 (by decide) = (3 : Fin 7)`
 * `(5 : Fin 9).subNat 0 (by decide) = (5 : Fin 9)`
 * `(3 : Fin 9).subNat 3 (by decide) = (0 : Fin 6)`
-/
@[inline] def subNat (m) (i : Fin (n + m)) (h : m ≤ i) : Fin n :=
  ⟨i - m, Nat.sub_lt_right_of_lt_add h i.2⟩

/--
The predecessor of a non-zero element of `Fin (n+1)`, with the bound decreased.

Examples:
 * `(4 : Fin 8).pred (by decide) = (3 : Fin 7)`
 * `(1 : Fin 2).pred (by decide) = (0 : Fin 1)`
-/
@[inline] def pred {n : Nat} (i : Fin (n + 1)) (h : i ≠ 0) : Fin n :=
  subNat 1 i <| Nat.pos_of_ne_zero <| mt (Fin.eq_of_val_eq (j := 0)) h

theorem val_inj {a b : Fin n} : a.1 = b.1 ↔ a = b := ⟨Fin.eq_of_val_eq, Fin.val_eq_of_eq⟩

theorem val_congr {n : Nat} {a b : Fin n} (h : a = b) : (a : Nat) = (b : Nat) :=
  Fin.val_inj.mpr h

theorem val_le_of_le {n : Nat} {a b : Fin n} (h : a ≤ b) : (a : Nat) ≤ (b : Nat) := h

theorem val_le_of_ge {n : Nat} {a b : Fin n} (h : a ≥ b) : (b : Nat) ≤ (a : Nat) := h

theorem val_add_one_le_of_lt {n : Nat} {a b : Fin n} (h : a < b) : (a : Nat) + 1 ≤ (b : Nat) := h

theorem val_add_one_le_of_gt {n : Nat} {a b : Fin n} (h : a > b) : (b : Nat) + 1 ≤ (a : Nat) := h

theorem exists_iff {p : Fin n → Prop} : (Exists fun i => p i) ↔ Exists fun i => Exists fun h => p ⟨i, h⟩ :=
  ⟨fun ⟨⟨i, hi⟩, hpi⟩ => ⟨i, hi, hpi⟩, fun ⟨i, hi, hpi⟩ => ⟨⟨i, hi⟩, hpi⟩⟩

end Fin
