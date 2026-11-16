import Lean
import Std.Tactic.Do

set_option sym.debug true

open Std.WP
set_option experimental.vcgen true

/-!
Regression test for #16364: `vcgen +jp` anti-unifies the arguments of the jumps to a join point,
so the join hypothesis states the parts of the states that all jumps agree on above the
disjunction over the jumps, and `grind` proves goals about those parts without a case split.
-/

-- The example of the module docstring of `Lean.Elab.Tactic.VCGen.JoinPoint`.
def f (n : Nat) : StateM (Nat × Nat) Nat := do
  let mut x := 0
  if n > 0 then x := 1 else
    x := 2
    modify fun (a, _) => (a, 0)
  return x + 1

/--
trace: case vc1
n : Nat
t : Nat × Nat
a✝² b✝¹ : Nat
a✝¹ : (a✝², b✝¹) = t
x✝¹ : PUnit
x✝ a✝ b✝ : Nat
h✝ : ∃ z, (a✝, b✝) = (a✝², z) ∧ (0 < n ∧ x✝ = 1 ∧ z = b✝¹ ∨ ¬0 < n ∧ x✝ = 2 ∧ z = 0)
⊢ a✝ = t.fst
-/
#guard_msgs in
example : ⦃fun s => s = t⦄ f n ⦃fun _ s => s.1 = t.1⦄ := by
  vcgen +jp [f]
  trace_state
  all_goals grind

structure S where
  pc : Nat
  r : Nat

structure W where
  pc : BitVec 32
  r : BitVec 32

/-- `n` sequential `if`s. Both branches add 4 to `pc`, and they add 1 or 2 to `r`. -/
syntax "diamonds% " num term:max : term
macro_rules
  | `(diamonds% $n $b) => do
    let rec go (i k : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      match k with
      | 0 => `(pure ())
      | k + 1 =>
        let idx := Lean.Syntax.mkNumLit (toString i)
        let rest ← go (i + 1) k
        `(do
            if $b $idx then modify (fun s => { s with pc := s.pc + 4, r := s.r + 1 })
            else modify (fun s => { s with pc := s.pc + 4, r := s.r + 2 })
            $rest:term)
    go 0 n.getNat

-- The reproducer of #16364.
example (b : Nat → Bool) (s₀ : S) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM S Unit) ⦃fun _ s => s.pc = s₀.pc + 48⦄ := by
  vcgen +jp with finish

-- The hull of each disjunction bounds its hole for `r`.
example (b : Nat → Bool) (s₀ : S) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM S Unit)
    ⦃fun _ s => s₀.r + 12 ≤ s.r ∧ s.r ≤ s₀.r + 24⦄ := by
  vcgen +jp with finish

-- The hole for `r` takes the value `n`, a local of the branch `some n`.
def step (o : Option Nat) : StateM S Unit := do
  match o with
  | some 0 => modify fun s => { s with pc := s.pc + 4, r := 0 }
  | some n => modify fun s => { s with pc := s.pc + 4, r := n }
  | none => modify fun s => { s with pc := s.pc + 4 }
  modify fun s => { s with pc := s.pc + 4 }

example (s₀ : S) :
    ⦃fun s => s = s₀⦄ step o ⦃fun _ s => s.pc = s₀.pc + 8⦄ := by
  vcgen +jp [step] with finish

/-- `n` sequential `match`es on `o i`. Alternative `0` sets `pc` to `0`, the other two add `4` to
`pc`, and all three add `1` to `r`. -/
syntax "spoiled% " num term:max : term
macro_rules
  | `(spoiled% $n $o) => do
    let rec go (i k : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      match k with
      | 0 => `(pure ())
      | k + 1 =>
        let idx := Lean.Syntax.mkNumLit (toString i)
        let rest ← go (i + 1) k
        `(do
            match ($o $idx : Nat) with
            | 0 => modify (fun s => { s with pc := 0, r := s.r + 1 })
            | 1 => modify (fun s => { s with pc := s.pc + 4, r := s.r + 1 })
            | _ => modify (fun s => { s with pc := s.pc + 4, r := s.r + 1 })
            $rest:term)
    go 0 n.getNat

-- One alternative spoils `pc`, so `pc` becomes a hole, and `r` stays above the disjunction. The
-- fields are `BitVec 32`, whose disjunctions have no hull.
example (o : Nat → Nat) (s₀ : W) :
    ⦃fun s => s = s₀⦄ (spoiled% 12 o : StateM W Unit) ⦃fun _ s => s.r = s₀.r + 12⦄ := by
  vcgen +jp with finish

-- A reassignment `s := e` in a branch passes a `let` local with the value `e`. The values
-- `s.r + 1` and `s.r * 2` of the locals `r` have no common part, so the hole for `r` takes the
-- locals as its values.
def addOrDouble (o : Nat) : StateM S Unit := do
  let mut s ← get
  match o with
  | 0 =>
    let r := s.r + 1
    s := { s with pc := s.pc + 4, r }
  | _ =>
    let r := s.r * 2
    s := { s with pc := s.pc + 4, r }
  set s

/--
trace: case vc1
o : Nat
s₀ s✝¹ : S
x✝¹ : PUnit
x✝ s✝ : S
h✝ :
  ∃ z,
    (x✝ = { pc := s₀.pc + 4, r := z } ∧ s✝ = s₀) ∧
      ((o = 0 ∧
          let r := s₀.r + 1;
          z = r) ∨
        ∃ x,
          (x = 0 → False) ∧
            o = x ∧
              let r := s₀.r * 2;
              z = r)
⊢ x✝.pc = s₀.pc + 4
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ addOrDouble o ⦃fun _ s => s.pc = s₀.pc + 4⦄ := by
  vcgen +jp [addOrDouble]
  trace_state
  all_goals grind

-- The `let` locals `x` have the values `x + 0` and `x + (0 + 1)`, with the common part `x + z`.
-- The hole values `0` and `0 + 1` are in `simp` normal form, so `simp` leaves the binder domain of
-- the join RHS unchanged.
def addZeroOrOne (c : Bool) : StateM Nat Unit := do
  let mut x ← get
  if c then x := x + 0 else x := x + (0 + 1)
  set x

/--
trace: case vc1
c : Bool
s₀ s✝¹ : Nat
x✝¹ : PUnit
x✝ s✝ : Nat
h✝ : ∃ z, (x✝ = s₀ + z ∧ s✝ = s₀) ∧ (c = true ∧ z = 0 ∨ ¬c = true ∧ z = 1)
⊢ s₀ ≤ x✝
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ addZeroOrOne c ⦃fun _ s => s₀ ≤ s⦄ := by
  vcgen +jp [addZeroOrOne]
  trace_state
  all_goals grind

-- The field `r` gets the argument of the parameter `x` at every jump, so it becomes `x` itself.
def storeX (c : Bool) (y : Nat) : StateM S Nat := do
  let mut x := 0
  if c then
    x := y + 1
    modify fun s => { s with r := x }
  else
    x := y * 2
    modify fun s => { s with r := x }
  return x

/--
trace: case vc1
c : Bool
y : Nat
s₀ s✝¹ : S
x✝¹ : PUnit
x✝ : Nat
s✝ : S
h✝ :
  s✝ = { pc := s₀.pc, r := x✝ } ∧
    ((c = true ∧
        let x := y + 1;
        x✝ = x) ∨
      ¬c = true ∧
        let x := y * 2;
        x✝ = x)
⊢ s✝.r = x✝
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ storeX c y ⦃fun x s => s.r = x⦄ := by
  vcgen +jp [storeX]
  trace_state
  all_goals grind
