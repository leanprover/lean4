/-!
# Tests for `match_goal` in `sym =>` mode
-/

opaque P : Nat → Prop
opaque Q : Nat → Prop
axiom p_succ : P n → P (n + 1)
axiom p_zero : P 0
axiom q_of_p : P n → Q n

/-! The alternative of the most specific matching pattern runs. -/

example : P 3 := by
  sym =>
    repeat
      match_goal with
      | P 0 => apply p_zero
      | P (_ + 1) => apply p_succ

example : Q 2 ∧ P 1 := by
  sym =>
    repeat
      match_goal with
      | _ ∧ _ => apply And.intro
      | Q _ => apply q_of_p
      | P 0 => apply p_zero
      | P (_ + 1) => apply p_succ

/-! An alternative with several patterns. -/

example : Q 1 := by
  sym =>
    repeat
      match_goal with
      | Q _ => apply q_of_p
      | P 0 | P (_ + 1) => first (apply p_zero) (apply p_succ)

/-! Patterns with binders, wildcards, and local variables. -/

example : P 0 → Q 0 := by
  sym =>
    match_goal with
    | _ → _ => intro h
    apply q_of_p
    tactic => exact h

example : P 0 := by
  sym =>
    match_goal with
    | Q _ => fail
    | _ => apply p_zero

example (n : Nat) (h : P n) : Q n := by
  sym =>
    match_goal with
    | Q 0 => fail
    | Q n => apply q_of_p
    tactic => exact h

/-! The order of the alternatives does not matter. -/

example : P 0 := by
  sym =>
    match_goal with
    | P _ => fail "general"
    | P 0 => apply p_zero

example : P 0 := by
  sym =>
    match_goal with
    | P 0 => apply p_zero
    | P _ => fail "general"

example : P 0 := by
  sym =>
    match_goal with
    | _ => fail "wildcard"
    | P _ => fail "general"
    | P 0 => apply p_zero

/-! A numeral is an instance of an offset pattern. -/

example : P 3 := by
  sym =>
    match_goal with
    | P (_ + 1) => fail "offset"
    | P 3 => apply p_succ
    apply p_succ; apply p_succ; apply p_zero

/-! Equally specific patterns of one alternative. -/

example : P 0 := by
  sym =>
    match_goal with
    | P _ | P _ => apply p_zero

/-! Failures. -/

/--
error: `match_goal` failed, no pattern matches the target
  P 0
-/
#guard_msgs in
example : P 0 := by
  sym =>
    match_goal with
    | Q _ => apply q_of_p

opaque F : Nat → Nat → Prop

/--
error: `match_goal` failed, the target
  F 0 0
matches the patterns
  F 0 _
  F _ 0
and no pattern among them is more specific than all others
-/
#guard_msgs in
example : F 0 0 := by
  sym =>
    match_goal with
    | F 0 _ => skip
    | F _ 0 => skip
    | F 1 1 => skip

/--
error: selected
case grind
⊢ P 0
-/
#guard_msgs in
example : P 0 := by
  sym =>
    match_goal with
    | P 0 => fail "selected"
    | P _ => apply p_zero

/-- error: tactic is only available in `sym =>` mode -/
#guard_msgs in
example : P 0 := by
  grind =>
    match_goal with
    | P 0 => skip

/-! A `match_goal` in a macro. All patterns of the expansion have the source range of the macro
call. The macro also uses a `Sym.simp` variant by name. -/

opaque R : Nat → Prop
axiom r_eq : R n = P n

register_sym_simp rToP where
  post := rewrite [r_eq]

macro "p_auto" : grind => `(grind|
  repeat
    match_goal with
    | R _ => simp rToP
    | P 0 => apply p_zero
    | P (_ + 1) => apply p_succ)

example : R 2 := by
  sym =>
    p_auto

example : P 5 := by
  sym =>
    p_auto
