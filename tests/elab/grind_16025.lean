/-!
Regression test for #16025: when the generated script performs more E-matching rounds than the
`ematch` limit allows without case splits, `grind?` raises the limit in its `grind only`
suggestions. In the original search, a case split pruned from the script reset the round counter.
-/

namespace Chain

def f0 (n : Nat) := n
def f1 (n : Nat) := n
def f2 (n : Nat) := n
def f3 (n : Nat) := n
def f4 (n : Nat) := n
def f5 (n : Nat) := n

@[grind =] theorem step0 (n : Nat) : f0 n = f1 n := rfl
@[grind =] theorem step1 (n : Nat) : f1 n = f2 n := rfl
@[grind =] theorem step2 (n : Nat) : f2 n = f3 n := rfl
@[grind =] theorem step3 (n : Nat) : f3 n = f4 n := rfl
@[grind =] theorem step4 (n : Nat) : f4 n = f5 n := rfl
@[grind =] theorem step5 (n : Nat) : f5 n = n := rfl

theorem irrelevant_split (n : Nat) : n = 0 ∨ n ≠ 0 := by grind
grind_pattern irrelevant_split => f0 n

/--
info: Try these:
  [apply] grind (ematch := 6) only [= step0, = step1, = step2, = step3, = step4, = step5]
  [apply] grind =>
    instantiate only [= step0]
    instantiate only [= step1]
    instantiate only [= step2]
    instantiate only [= step3]
    instantiate only [= step4]
    instantiate only [= step5]
-/
#guard_msgs in
example (n : Nat) : f0 n = n := by grind?

example (n : Nat) : f0 n = n := by
  grind (ematch := 6) only [= step0, = step1, = step2, = step3, = step4, = step5]

end Chain

namespace Step

variable (P : Nat → Prop) (p q : Prop) (step : ∀ n, P n → P (n + 1)) (base : P 0)

/--
info: Try these:
  [apply] grind (ematch := 6) only [#68b6]
  [apply] grind (ematch := 6) only
  [apply] grind =>
    instantiate only [#68b6]
    instantiate only [#68b6]
    instantiate only [#68b6]
    instantiate only [#68b6]
    instantiate only [#68b6]
    lia
    instantiate only [#68b6]
-/
#guard_msgs in
example (_ : p ∨ q) : P 12 := by grind?

example (_ : p ∨ q) : P 12 := by grind (ematch := 6) only [#68b6]

example (_ : p ∨ q) : P 12 := by grind (ematch := 6) only

end Step

-- Within the limit, the configuration is unchanged.
/--
info: Try these:
  [apply] grind only [= Nat.min_def, #35e2, #10ba]
  [apply] grind only [= Nat.min_def]
  [apply] grind =>
    instantiate only [= Nat.min_def]
    cases #35e2 <;> cases #10ba
-/
#guard_msgs in
example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by grind?
