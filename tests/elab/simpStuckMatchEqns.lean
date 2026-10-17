import Lean
/-!
When `simp` cannot reduce a `match`, it tries to rewrite it with the `match` equation theorems.
The left-hand side of such a theorem applies the matcher to the patterns of one alternative, so it
cannot apply to a partial application of the matcher, nor when a discriminant is a local variable
(without a value, and not a proof) while the pattern at that position is a constructor application
of a type that is not a non-recursive structure. This file checks which equation theorems `simp`
tries for such a stuck `match`, and that it still uses the equation theorems that do apply.
-/
open Lean

set_option Elab.async false

inductive Op where
  | inc | dbl

def Op.effect : Op → Nat → Nat
  | .inc, s => s + 1
  | .dbl, s => s * 2

def block (ops : List Op) (s : Nat) : Nat := ops.foldl (fun t op => op.effect t) s

def matchEqnsGenerated (matcher : Name) : CoreM Bool :=
  return (← getEnv).contains (mkPrivateName (← getEnv) matcher ++ `splitter)

/-!
`Op.effect.eq_def` unfolds `Op.effect` in the step function `fun t op => op.effect t`, where `op` is
a variable, so the `match` is stuck. (`Op.effect.eq_def` is used because generating the equation
theorems of `Op.effect`, as `simp [Op.effect]` would do, generates the `match` equation theorems
anyway.)
-/

#guard_msgs in
set_option trace.Meta.Tactic.simp.unify true in
theorem block_eq (s : Nat) : block [.inc, .dbl] s = (s + 1) * 2 := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect.eq_def]

/-- info: false -/
#guard_msgs in
#eval matchEqnsGenerated ``Op.effect.match_1

/-! Equation theorems whose pattern at the variable discriminant is a variable are still tried. -/

def Op.cost (op : Op) : Nat :=
  match op with
  | .inc => 1
  | _ => 2

theorem cost_eq (op : Op) (h : op ≠ .inc) : op.cost = 2 := by
  simp [Op.cost.eq_def]

/-- info: true -/
#guard_msgs in
#eval matchEqnsGenerated ``Op.cost.match_1

example (op : Op) (h : op ≠ .inc) (n : Nat) : (match op, n with | .inc, _ => 1 | _, m => m + 2) = n + 2 := by
  simp

-- An over-applied matcher.
example (op : Op) (h : op ≠ .inc) (n : Nat) :
    (match op with | .inc => fun x => x | _ => fun x => x + 1) n = n + 1 := by
  simp

-- `match h : _ with`
example (op : Op) (h : op ≠ .inc) : (match hop : op with | .inc => 1 | _ => 2) = 2 := by
  simp

-- Literal patterns.
example (n : Nat) (h : n ≠ 0) : (match n with | 0 => 1 | _ => 2) = 2 := by
  simp

/-!
`simp` does not fail on a stuck `match` whose equation theorems cannot be generated
(see `issue2237.lean`).
-/

inductive Ty where
  | star

inductive Lookup : List Ty → Ty → Type where
  | z : Lookup (t :: Γ) t

inductive Tm : List Ty → Ty → Type where
  | var : Lookup Γ a → Tm Γ a
  | lam : Tm (.star :: Γ) .star → Tm Γ .star
  | ap : Tm Γ .star → Tm Γ .star → Tm Γ .star

def Tm.tag (t : Tm Γ a) : Nat :=
  match t with
  | .var _ => 0
  | .lam _ => 1
  | .ap (.lam _) _ => 2
  | .ap _ _ => 3

example (t : Tm Γ a) (p : Nat → Prop) (h : p t.tag) : p t.tag := by
  simp [Tm.tag]
  exact h
