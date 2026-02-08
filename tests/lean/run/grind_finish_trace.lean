open Lean Grind

/--
info: Try these:
  [apply] cases #e4c4 <;> cases #3e9f <;> ring
  [apply] finish only [#e4c4, #3e9f]
-/
#guard_msgs in
example {α : Type} [CommRing α] (a b c d e : α) :
    (a * a = b * c ∨ a^2 = c * b) →
    (a^2 = c * b ∨ e^2 = d * c) →
    (b^2 = d*c ∨ b^2 = c*d) →
    a*b*(b*a) = c^2*b*d := by
 grind => finish?


/--
info: Try these:
  [apply] ⏎
    cases #6c8c
    · cases #4228
    · cases #4228 <;> lia
  [apply] finish only [#6c8c, #4228]
-/
#guard_msgs in
example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind => finish?

/-- error: tactic is not applicable -/
#guard_msgs in
example (a b c : Int) : a + b ≤ 2 → b = c → 2*b - c + a ≤ 3 := by
  grind => cases_next

example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind =>
    cases_next <;> cases_next <;> cases_next <;> cases_next <;> lia

example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind =>
    repeat (first (lia) (cases_next))

example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind =>
    repeat (first (cases_next) (lia))

example (p : Nat → Prop) (x y z w : Int) :
    (x = 1 ∨ x = 2) →
    (w = 1 ∨ w = 4) →
    (y = 1 ∨ (∃ x : Nat, y = 3 - x ∧ p x)) →
    (z = 1 ∨ z = 0) → x + y ≤ 6 := by
  grind =>
    repeat (first (ring) (cases_next) (lia))

/--
info: Try these:
  [apply] cases #5d93 <;> cases #11de <;> ac
  [apply] finish only [#5d93, #11de]
-/
#guard_msgs in
example {α : Type} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d e : α) :
    (op a a = op b c ∨ op a a = op c b) →
    (op a a = op c b ∨ op e e = op d c) →
    (op b b = op d c ∨ op b b = op c d) →
    op (op a b) (op b a) = op (op c c) (op b d) := by
  grind => finish?

/--
info: Try these:
  [apply] ⏎
    instantiate only [= Array.getElem_set]
    instantiate only [= Array.getElem_set]
  [apply] finish only [= Array.getElem_set]
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
    cases #e4c4
    · cases #7fb4
      · ring
      · sorry
    · cases #7fb4
      · ring
      · sorry
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
    cases #d485
    · sorry
    · lia
-/
#guard_msgs in
example (as : Array α) (lo hi i j : Nat) (h₁ : lo ≤ i) (_ : i < j) (_ : j ≤ hi) (_ : j < as.size)
    (_ : ¬as.size = 0) : min lo (as.size - 1) < i := by
  grind => finish?

/--
info: Try these:
  [apply] ⏎
    instantiate only [= getMsbD_setWidth']
    cases #1f39
  [apply] finish only [= getMsbD_setWidth', #1f39]
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
    cases #c2c1

/--
info: Try these:
  [apply] cases #52a6 <;>
      instantiate only [= BitVec.getElem_and] <;> instantiate only [= BitVec.getElem_or] <;> cases #de0f
  [apply] finish only [= BitVec.getElem_and, = BitVec.getElem_or, #52a6, #de0f]
-/
#guard_msgs in
example (x y : BitVec 64) : (x ||| y) &&& x = x := by
  grind => finish?

set_option trace.Meta.debug true in
example (x y : BitVec 64) : (x ||| y) &&& x = x := by
  grind => finish?


macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

/--
info: Try these:
  [apply] ⏎
    instantiate only [= Array.getElem_set]
    ring
  [apply] finish only [= Array.getElem_set]
-/
#guard_msgs in
example (a : Array (BitVec 64)) (i : Nat) (v : BitVec 64)
    : (_ : i < a.size) → (_ : i + 1 < a.size) → (a.set i v)[i+1] + a[i+1] = 2*a[i+1] := by
  grind => finish?

/--
info: Try these:
  [apply] ⏎
    mbtc
    cases #aceb
  [apply] finish only [#aceb]
-/
#guard_msgs in
example (f : Nat → Nat) (x : Nat)
    : x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  grind => finish?

/--
info: Try these:
  [apply] ⏎
    mbtc
    cases #cb64
  [apply] finish only [#cb64]
-/
#guard_msgs in
example (f : Int → Int → Int) (x y : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x y = 2 → f 1 y = 2 := by
  grind => finish?

example (f : Int → Int → Int) (x y : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x y = 2 → f 1 y = 2 := by
  grind =>
    -- We can use `have` to golf proofs using `mbtc` and `cases`
    have : x = 1

example (f : Int → Int) (x y : Int)
    : 0 ≤ x → x ≤ 2 → f 0 = y → f 1 = y → f 2 = y → f x = y := by
  grind

example (f : Int → Int) (x y : Int)
    : 0 ≤ x → x ≤ 2 → f 0 = y → f 1 = y → f 2 = y → f x = y := by
  grind =>
    mbtc
    cases #ae37 <;> mbtc <;> cases #cb64 <;> mbtc <;> cases #de9d

example (f : Int → Int) (x y : Int)
    : 0 ≤ x → x ≤ 2 → f 0 = y → f 1 = y → f 2 = y → f x = y := by
  grind =>
    -- Again, we can use `have` to golf the proof with `mbtc`
    have : x ≠ 0
    have : x ≠ 1
    have : x ≠ 2

example (f g : Int → Int) (x y z w : Int)
    : 0 ≤ x → x ≤ 1 → 0 ≤ w →
      g 0 = z → g 1 = z → g 2 = z →
      f 0 = y → f 1 = y →
      g w ≠ z → f x = y := by
  set_option trace.grind.split true in
  grind =>
    mbtc
    cases #ae37
    mbtc
    cases #cb64

/--
trace: [grind.split] w = 0, generation: 0
[grind.split] x = 0, generation: 0
[grind.split] w = 1, generation: 0
[grind.split] x = 1, generation: 0
-/
#guard_msgs in
example (f g : Int → Int) (x y z w : Int)
    : 0 ≤ x → x ≤ 1 → 0 ≤ w →
      g 0 = z → g 1 = z → g 2 = z →
      f 0 = y → f 1 = y →
      g w ≠ z → f x = y := by
  set_option trace.grind.split true in
  grind

/--
trace: [grind.split] x = 0, generation: 0
[grind.split] x = 1, generation: 0
-/
#guard_msgs in
example (f g : Int → Int) (x y z w : Int)
    : 0 ≤ x → x ≤ 1 → 0 ≤ w →
      g 0 = z → g 1 = z → g 2 = z →
      f 0 = y → f 1 = y →
      g w ≠ z → f x = y := by
  fail_if_success grind [#23ad] -- not possible to solve using this set of anchors.
  set_option trace.grind.split true in
  grind only [#ae37, #cb64] -- Only these two splits were performed.

/--
trace: [grind.split] x = 0, generation: 0
[grind.split] x = 1, generation: 0
-/
#guard_msgs in
example (f g : Int → Int) (x y z w : Int)
    : 0 ≤ x → x ≤ 1 → 0 ≤ w →
      g 0 = z → g 1 = z → g 2 = z →
      f 0 = y → f 1 = y →
      g w ≠ z → f x = y := by
  set_option trace.grind.split true in
  grind =>
    finish only [#ae37, #cb64]

/--
trace: [grind.ematch.instance] h: f (f a) = f a
[grind.ematch.instance] h: f (f (f a)) = f (f a)
[grind.ematch.instance] h: f (f (f (f a))) = f (f (f a))
[grind.ematch.instance] h_1: g (g (g b)) = g (g b)
[grind.ematch.instance] h_1: g (g b) = g b
-/
#guard_msgs in
example (f g : Int → Int)
    (_ : ∀ x, f (f x) = f x)
    (_ : ∀ x, g (g x) = g x)
    (a b : Int)
    (_ : g (g b) = b)
    : f (f (f a)) = f a := by
  set_option trace.grind.ematch.instance true in
  grind

/--
trace: [grind.ematch.instance] x✝²: f (f a) = f a
[grind.ematch.instance] x✝²: f (f (f a)) = f (f a)
[grind.ematch.instance] x✝²: f (f (f (f a))) = f (f (f a))
-/
#guard_msgs in
example (f g : Int → Int)
    (_ : ∀ x, f (f x) = f x)
    (_ : ∀ x, g (g x) = g x)
    (a b : Int)
    (_ : g (g b) = b)
    : f (f (f a)) = f a := by
  set_option trace.grind.ematch.instance true in
  grind only [#7a0d]

/--
trace: [grind.ematch.instance] x✝²: f (f a) = f a
[grind.ematch.instance] x✝²: f (f (f a)) = f (f a)
[grind.ematch.instance] x✝²: f (f (f (f a))) = f (f (f a))
-/
#guard_msgs in
example (f g : Int → Int)
    (_ : ∀ x, f (f x) = f x)
    (_ : ∀ x, g (g x) = g x)
    (a b : Int)
    (_ : g (g b) = b)
    : f (f (f a)) = f a := by
  set_option trace.grind.ematch.instance true in
  grind => finish only [#7a0d]
