open Lean Grind

/--
info: Try this:
  [apply] cases #c4b6 <;> cases #4c68 <;> ring
-/
#guard_msgs in
example {α : Type} [CommRing α] (a b c d e : α) :
    (a * a = b * c ∨ a^2 = c * b) →
    (a^2 = c * b ∨ e^2 = d * c) →
    (b^2 = d*c ∨ b^2 = c*d) →
    a*b*(b*a) = c^2*b*d := by
 grind => finish?


/--
info: Try this:
  [apply] ⏎
    cases #b0f4
    next => cases #50fc
    next => cases #50fc <;> lia
-/
#guard_msgs in
example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind => finish?

/--
info: Try this:
  [apply] cases #5c4b <;> cases #896f <;> ac
-/
#guard_msgs in
example {α : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d e : α) :
    (op a a = op b c ∨ op a a = op c b) →
    (op a a = op c b ∨ op e e = op d c) →
    (op b b = op d c ∨ op b b = op c d) →
    op (op a b) (op b a) = op (op c c) (op b d) := by
  grind => finish?

/--
info: Try this:
  [apply] ⏎
    instantiate only [= Array.getElem_set]
    instantiate only [= Array.getElem_set]
-/
#guard_msgs in
example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : bs = as.set i₁ v₁)
        (h₃ : i₂ < bs.size)
        (h₃ : cs = bs.set i₂ v₂)
        (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind => finish?

set_option warn.sorry false

/--
info: Try this:
  [apply] ⏎
    cases #c4b6
    next =>
      cases #8c9f
      next => ring
      next => sorry
    next =>
      cases #8c9f
      next => ring
      next => sorry
-/
#guard_msgs in
example {α : Type} [CommRing α] (a b c d e : α) :
    (a^2 = c * b ∨ e^2 = d * c) →
    (b^2 = d*c ∨ b^2 = c*d) →
    a*b*(b*a) = c^2*b*d := by
 grind => finish?

/--
info: Try this:
  [apply] ⏎
    instantiate only [= Nat.min_def]
    cases #7640
    next => sorry
    next => lia
-/
#guard_msgs in
example (as : Array α) (lo hi i j : Nat) (h₁ : lo ≤ i) (_ : i < j) (_ : j ≤ hi) (_ : j < as.size)
    (_ : ¬as.size = 0) : min lo (as.size - 1) < i := by
  grind => finish?

/--
info: Try this:
  [apply] ⏎
    instantiate only [= getMsbD_setWidth']
    cases #aa9d
-/
#guard_msgs in
open BitVec in
example (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getMsbD (setWidth' ge x) i = (decide (m - n ≤ i) && getMsbD x (i + n - m)) := by
  grind => finish?

open BitVec in
example (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getMsbD (setWidth' ge x) i = (decide (m - n ≤ i) && getMsbD x (i + n - m)) := by
  grind =>
    instantiate only [= getMsbD_setWidth']
    cases #aa9d

/--
info: Try this:
  [apply] cases #9942 <;>
      instantiate only [= BitVec.getElem_and] <;> instantiate only [= BitVec.getElem_or] <;> cases #cfbc
-/
#guard_msgs in
example (x y : BitVec 64) : (x ||| y) &&& x = x := by
  grind => finish?

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

/--
info: Try this:
  [apply] ⏎
    instantiate only [= Array.getElem_set]
    ring
-/
#guard_msgs in
example (a : Array (BitVec 64)) (i : Nat) (v : BitVec 64)
    : (_ : i < a.size) → (_ : i + 1 < a.size) → (a.set i v)[i+1] + a[i+1] = 2*a[i+1] := by
  grind => finish?
