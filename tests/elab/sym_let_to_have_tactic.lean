import Lean
set_option warn.sorry false

/-!
Tests for the `let_to_have` tactic in `sym =>` mode. It converts the nondependent
`let` declarations of the goal target into `have` declarations, fails when it makes no
progress, and keeps genuinely dependent `let`s (see `tests/elab/sym_letToHave.lean` for
the verdict families of the underlying `Sym.letToHave`).
-/

-- Converts the nondependent `let`: makes progress, no error.
/--
trace: case grind
⊢ (have x := 10; x + 1) = 11
-/
#guard_msgs (whitespace := lax) in
example : (let x := 10; x + 1) = 11 := by
  sym => let_to_have; show_goals; sorry

-- The target only has a `have`: no progress.
/-- error: `let_to_have` made no progress -/
#guard_msgs in
example : (have x := 10; x + 1) = 11 := by
  sym => let_to_have; sorry

-- A genuinely dependent `let`: the domain `G x` has type `H x`, which is a sort only
-- after zeta-unfolding `x`. The `let` is kept, so no progress.
def H : Bool → Type 1 := fun b => match b with | true => Type | false => Type
axiom G : (b : Bool) → H b

/-- error: `let_to_have` made no progress -/
#guard_msgs in
example : (let x := true; ∀ (_ : G x), True) := by
  sym => let_to_have; sorry

/--
trace: case grind
⊢ (have x := 10; x + 1) = have x := 10; 1 + x
-/
#guard_msgs (whitespace := lax) in
example : (let x : Nat := 10; x + 1) = (have x : Nat := 10; 1 + x) := by
  sym => let_to_have; show_goals; finish

-- A telescope: both `let`s are converted.
/--
trace: case grind
⊢ (have a := 1; have b := a + 1; a + b) = 3
-/
#guard_msgs (whitespace := lax) in
example : (let a := 1; let b := a + 1; a + b) = 3 := by
  sym => let_to_have; show_goals; sorry

-- Mixed verdicts in one target: `x` is dependent (the value of `h` needs `x ≡ 1`),
-- `h` is not.
set_option linter.unusedVariables false in
/--
trace: case grind
⊢ (let x := 1; have h := ⋯; x + 1) = 2
-/
#guard_msgs (whitespace := lax) in
example : (let x : Nat := 1; let h : x = 1 := rfl; x + 1) = 2 := by
  sym => let_to_have; show_goals; sorry

-- A lambda value mentioning the outer `let` variable (`checkFun` through the `let`
-- annotation obligation).
/--
trace: case grind
⊢ (have x := 5; have f := fun y => y + x; f 1) = 6
-/
#guard_msgs (whitespace := lax) in
example : (let x := 5; let f := fun y => y + x; f 1) = 6 := by
  sym => let_to_have; show_goals; sorry

-- A closure argument mentioning the `let` variable (`checkFun` through `checkApp`).
/--
trace: case grind
⊢ (have x := 5; List.foldl (fun a b => a + b + x) 0 [1]) = 6
-/
#guard_msgs (whitespace := lax) in
example : (let x := 5; List.foldl (fun a b => a + b + x) 0 [1]) = 6 := by
  sym => let_to_have; show_goals; sorry

-- The `let` annotation is a type alias: `ensureForall` must use `whnf` to expose the
-- expected function type in `checkFun`.
def NatFun := Nat → Nat

/--
trace: case grind
⊢ (have x := 5; have f := fun y => y + x; f 1) = 6
-/
#guard_msgs (whitespace := lax) in
example : (let x := 5; let f : NatFun := fun y => y + x; f 1) = 6 := by
  sym => let_to_have; show_goals; sorry

-- A `∀`-telescope whose terminal body mentions the `let` variable (terminal `getLevel`
-- obligation in `visitForall`).
/--
trace: case grind
⊢ have b := true; ∀ (n : Nat), b = (n == n)
-/
#guard_msgs (whitespace := lax) in
example : (let b := true; ∀ (n : Nat), b = (n == n)) := by
  sym => let_to_have; show_goals; sorry

-- A projection whose struct mentions the `let` variable (projection obligation).
/--
trace: case grind
⊢ (have p := (1, 2); p.fst) = 1
-/
#guard_msgs (whitespace := lax) in
example : (let p := (1, 2); p.1) = 1 := by
  sym => let_to_have; show_goals; sorry

-- The same closed `let` subterm on both sides: pointer-shared, visited once, both
-- occurrences converted.
/--
trace: case grind
⊢ (have x := 5; x + 1) = have x := 5; x + 1
-/
#guard_msgs (whitespace := lax) in
example : (let x := 5; x + 1) = (let x := 5; x + 1) := by
  sym => let_to_have; show_goals; finish

-- Metavariables are opaque values: the `let` is converted even though the target
-- contains `?y`, and `?y` is not assigned.
/--
trace: case grind
⊢ (have x := 10; x + 1) = ?y
-/
#guard_msgs (whitespace := lax) in
example : ∃ y, (let x := 10; x + 1) = y := by
  refine ⟨?y, ?_⟩
  rotate_left
  sym => let_to_have; show_goals; sorry
  exact 11
