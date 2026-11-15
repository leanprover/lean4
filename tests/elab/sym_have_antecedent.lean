import Lean
import Std.Tactic.Do

set_option sym.debug true

open Std.WP
set_option experimental.vcgen true

/-!
Tests that `Sym` backward rules keep the `have`s of their antecedents, which become new goals,
and zeta-reduce `have`s in patterns and on the binder spine (#16122).
-/

opaque P : Nat → Prop
opaque Q : Nat → Prop
opaque R : Nat → Prop
opaque g : Nat → Nat

/-! ## `sym => apply`: `have`s in antecedents are kept -/

axiom a1 (x : Nat) (h : have y := x + 1; P y ∧ P y) : P (x + 1)
/--
trace: x : Nat
⊢ have y := x + 1;
  P y ∧ P y
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : P (x + 1) := by
  sym => apply a1; show_goals; sorry

-- Nested `have`s.
axiom a2 (x : Nat) (h : have a := x + 1; have b := a * a; P b ∧ P b) : Q x
/--
trace: x : Nat
⊢ have a := x + 1;
  have b := a * a;
  P b ∧ P b
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q x := by
  sym => apply a2; show_goals; sorry

-- A `have` under a binder.
axiom a3 (x : Nat) (h : ∀ z, have y := g (z + x); P y ∧ P y) : Q x
/--
trace: x : Nat
⊢ ∀ (z : Nat),
    have y := g (z + x);
    P y ∧ P y
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q x := by
  sym => apply a3; show_goals; sorry

-- The value is instantiated from the goal once, not copied to each use.
axiom a4 (x : Nat) (h : have y := x; P y ∧ P y ∧ P y) : Q x
/--
trace: x : Nat
⊢ have y := g (g (g x));
  P y ∧ P y ∧ P y
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q (g (g (g x))) := by
  sym => apply a4; show_goals; sorry

-- A rule from a local hypothesis (`mkBackwardRuleFromExpr`).
/--
trace: x : Nat
h :
  (have y := g x;
    P y ∧ P y) →
    Q x
⊢ have y := g x;
  P y ∧ P y
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) (h : (have y := g x; P y ∧ P y) → Q x) : Q x := by
  sym => apply h; show_goals; sorry

axiom a7 (x : Nat) (h : P x) : Q x

-- A nondependent `let` becomes a `have`.
axiom c0 (x : Nat) (h : let y := g x; P y ∧ P y) : Q x
/--
trace: x : Nat
⊢ have y := g x;
  P y ∧ P y
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q x := by
  sym => apply c0; show_goals; sorry

-- A `have` in the domain of a pattern variable that matching assigns, so the type is checked.
axiom th (f : have n := Nat; n → Nat) : Q (f 0)
example : Q (g 0) := by
  sym => apply th

-- A universe-polymorphic rule.
universe u
opaque PU : {α : Sort u} → α → Prop
axiom up {α : Sort u} (a : α) (h : have b := a; b = b) : PU a
/--
trace: ⊢ have b := 0;
  b = b
-/
#guard_msgs (trace, drop warning) in
example : PU (0 : Nat) := by
  sym => apply up; show_goals; sorry

/-! ## Zeta-reduced -/

-- A dependent `let` in an antecedent.
axiom c1 (h : let α := Nat; ∀ a : α, a + 0 = a) : Q 0
/-- trace: ⊢ ∀ (a : Nat), a + 0 = a -/
#guard_msgs (trace, drop warning) in
example : Q 0 := by
  sym => apply c1; show_goals; sorry

-- A `have` on the binder spine.
axiom c2 (x : Nat) : have y := g x; P y → Q y
/--
trace: x : Nat
⊢ P (g x)
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q (g x) := by
  sym => apply c2; show_goals; sorry

-- A `have` in the conclusion.
axiom c3 (x : Nat) (h : P x) : have y := g x; Q y
/--
trace: x : Nat
⊢ P x
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q (g x) := by
  sym => apply c3; show_goals; sorry

-- With `num? := some 1`, the second binder is part of the pattern.
axiom c4 (x : Nat) (h : have y := g x; P y) : Q x
open Lean Meta Sym in
/-- info: false -/
#guard_msgs in
#eval show MetaM Bool from do
  let p ← mkPatternFromDecl ``c4 (some 1)
  return (p.pattern.find? (·.isLet)).isSome

/-! ## `isDefEqS` zeta-reduces `let`s and `have`s in terms -/

example (n : Nat) : (have t := n; t) = n := by
  sym => apply Eq.refl

example (n : Nat) : (let t := n; t) = n := by
  sym => apply Eq.refl

-- A chain, where a later value applies an earlier one.
example (n : Nat) : (have a := n; have f := fun x => x + a; have y := f 0; y) = 0 + n := by
  sym => apply Eq.refl

-- `let`s on both sides that are equal only after zeta-reduction.
example (n : Nat) : (have a := n; a + 1) = (have b := n; have c := b; c + 1) := by
  sym => apply Eq.refl

-- A `have` under a binder.
example : (fun x : Nat => have y := x; y + 1) = (fun x => x + 1) := by
  sym => apply Eq.refl

-- A term that is not maximally shared.
open Lean Meta Sym in
/-- info: true, false -/
#guard_msgs in
run_meta SymM.run do
  let g0 := mkApp (mkConst ``g) (mkNatLit 0)
  let e : Expr := .letE `y (mkConst ``Nat) g0 (mkNatAdd (.bvar 0) (.bvar 0)) true
  logInfo m!"{← isDefEqS e (mkNatAdd g0 g0)}, {← isMaxShared e}"

-- `isDefEqS` assigns a metavariable the `let`/`have` itself, not its zeta-reduction, in both
-- directions.
open Lean Meta Sym in
/--
info: true: let y := g 0;
y + y
---
info: true: let y := g 0;
y + y
---
info: true: have y := g 0;
y + y
---
info: true: have y := g 0;
y + y
-/
#guard_msgs in
run_meta SymM.run do
  for nondep in [false, true] do
    let e ← shareCommon <| .letE `y (mkConst ``Nat) (mkApp (mkConst ``g) (mkNatLit 0))
      (mkNatAdd (.bvar 0) (.bvar 0)) nondep
    for swap in [false, true] do
      let m ← mkFreshExprMVar (mkConst ``Nat)
      let r ← if swap then isDefEqS e m else isDefEqS m e
      logInfo m!"{r}: {← instantiateMVars m}"

-- Matching a pattern against a term zeta-reduces the `let`s and `have`s of the term.
axiom pAll (x : Nat) : P x
example (x : Nat) : have y := g x; P y := by
  sym => apply pAll

axiom pg (x : Nat) : P (g x)
example (x : Nat) : P (have y := g x; y) := by
  sym => apply pg

axiom qgg (x y : Nat) : Q (g x + g y)
example (x : Nat) : Q (g x + have f := g; f (x + 1)) := by
  sym => apply qgg

-- A `have` at the head of an application.
example (x : Nat) : P ((have f := g; f) x) := by
  sym => apply pg

-- A literal pattern.
opaque S : String → Prop
axiom sa : S "a"
example : S (have s := "a"; s) := by
  sym => apply sa

-- An offset pattern.
axiom psucc (x : Nat) : P (x + 1)
example (n : Nat) : P (have y := n; y + 1) := by
  sym => apply psucc
example (n : Nat) : P (have y := n + 1; y + 1) := by
  sym => apply psucc

-- An instance argument (checked by `isDefEqI`).
opaque R2 : (α : Type) → [Inhabited α] → α → Prop
axiom ri (x : Nat) : R2 Nat x
example : @R2 Nat (have i := instInhabitedNat; i) 0 := by
  sym => apply ri

-- A `have` under metadata.
open Lean Meta Sym in
/-- info: [g 0] -/
#guard_msgs in
run_meta SymM.run do
  let p ← mkPatternFromDecl ``pAll
  let e ← shareCommon <| .mdata {} <| .letE `y (mkConst ``Nat) (mkApp (mkConst ``g) (mkNatLit 0))
    (mkApp (mkConst ``P) (.bvar 0)) true
  let some r ← p.match? e | throwError "no match"
  logInfo m!"{r.args}"

-- A pattern variable is assigned the `have`, not its zeta-reduction.
/--
trace: x : Nat
⊢ P
    (have y := g x;
    y)
-/
#guard_msgs (trace, drop warning) in
example (x : Nat) : Q (have y := g x; y) := by
  sym => apply a7; show_goals; sorry

/-! ## `vcgen +jp` shares the join points of an unfolded definition -/

elab "goal_count" : tactic => do
  Lean.logInfo m!"{(← Lean.Elab.Tactic.getGoals).length} goals"

/-- `n` sequential `if`s (#16122). -/
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
            if $b $idx then modify (· + 1) else modify (· + 2)
            $rest:term)
    go 0 n.getNat

def prog3 (b : Nat → Bool) : StateM Nat Unit := diamonds% 3 b

/-- info: 2 goals -/
#guard_msgs in
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ prog3 b ⦃fun _ s => s₀ + 3 ≤ s ∧ s ≤ s₀ + 6⦄ := by
  unfold prog3
  vcgen +jp
  goal_count
  all_goals lia

-- The antecedent `wp rhs …` of the unfold rule keeps `have __do_jp`.
/-- info: 2 goals -/
#guard_msgs in
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ prog3 b ⦃fun _ s => s₀ + 3 ≤ s ∧ s ≤ s₀ + 6⦄ := by
  vcgen +jp [prog3.eq_def]
  goal_count
  all_goals lia

/-- info: 2 goals -/
#guard_msgs in
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ prog3 b ⦃fun _ s => s₀ + 3 ≤ s ∧ s ≤ s₀ + 6⦄ := by
  vcgen +jp [prog3]
  goal_count
  all_goals lia

-- `vcgen` introduces the `have` of the precondition.
axiom modify_spec' (f : Nat → Nat) (Q : Unit → Nat → Prop) :
    ⦃fun s => have s' := f s; Q () s' ∨ R s'⦄ (modify f : StateM Nat Unit) ⦃Q⦄

/--
trace: case vc1
s₀ s✝ : Nat
s' : Nat := g s₀
⊢ R s' ∨ R s'
-/
#guard_msgs (trace, drop warning) in
example (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ (modify g : StateM Nat Unit) ⦃fun _ s => R s⦄ := by
  vcgen [modify_spec']
  trace_state
  all_goals sorry

-- `vcgen` continues with the program after the `have` of a precondition. It simplifies the value
-- and substitutes a literal value.
def bump : StateM Nat Unit := modify (· * 2)

def keep : StateM Nat Unit := modify id

axiom bump_spec {Q : Unit → Nat → Prop} :
    ⦃fun s => have v := s * 2; ∀ b : Bool, Q () (if b then v else v)⦄ bump ⦃Q⦄

axiom keep_spec {Q : Unit → Nat → Prop} :
    ⦃fun s => have v := s; ∀ b : Bool, Q () (if b then v else v)⦄ keep ⦃Q⦄

example : ⦃fun _ => True⦄ (do bump; bump : StateM Nat Unit) ⦃fun _ s => s = s⦄ := by
  vcgen [bump_spec]

-- The first value `1 * 2` simplifies to the literal `2`, which `vcgen` substitutes. The second
-- value `(if b then 2 else 2) * 2` is introduced.
/--
trace: case vc1
s✝ : Nat
x✝¹ : Bool
v : Nat := (if x✝¹ = true then 2 else 2) * 2
x✝ : Bool
⊢ 0 < if x✝ = true then v else v
-/
#guard_msgs (trace, drop warning) in
example : ⦃fun s => s = 1⦄ (do bump; bump : StateM Nat Unit) ⦃fun _ s => 0 < s⦄ := by
  vcgen [bump_spec]
  trace_state
  all_goals sorry

-- The value `s` becomes the literal `1`, which `vcgen` substitutes.
/--
trace: case vc1
s✝ : Nat
x✝ : Bool
⊢ 0 < if x✝ = true then 1 else 1
-/
#guard_msgs (trace, drop warning) in
example : ⦃fun s => s = 1⦄ (keep : StateM Nat Unit) ⦃fun _ s => 0 < s⦄ := by
  vcgen [keep_spec]
  trace_state
  all_goals sorry

-- The type of the program depends on the value of the `let`, so `vcgen` keeps the value
-- `0 + (k + 3)` as written and introduces `n`.
example (k : Nat) : ⦃fun _ => True⦄
    (let n := 0 + (k + 3); (pure (⟨0, Nat.zero_lt_succ _⟩ : Fin n) : StateM Nat (Fin n)))
    ⦃fun r _ => r.val = 0⦄ := by
  vcgen simp [Nat.zero_add]

-- A struct update elaborates to `have __src := s.m; …`, which reaches `isDefEqS` in `cleanupVC`.
structure M where
  x : Nat
  y : Nat

structure St where
  m : M
  b : Nat

def setX (k : Nat) : StateM St Unit :=
  modify fun s => { s with m := { s.m with x := k } }

theorem modify_spec (f : St → St) (Q : Unit → St → Prop) :
    ⦃fun s => Q () (f s)⦄ (modify f : StateM St Unit) ⦃Q⦄ := by
  vcgen [modify] with finish

example (s₀ : St) (k : Nat) :
    ⦃fun s => s = s₀⦄ setX k ⦃fun _ s' => s'.m = { x := k, y := s₀.m.y }⦄ := by
  vcgen [setX, modify_spec]

-- `vcgen` keeps the value of a `have` in the program as written, even if its simp set rewrites it.
/--
trace: case vc1
k s✝ : Nat
x : Nat := 0 + k
⊢ x + x = k + k
-/
#guard_msgs (trace, drop warning) in
example (k : Nat) :
    ⦃fun _ => True⦄ (have x := 0 + k; pure (x + x) : StateM Nat Nat) ⦃fun r _ => r = k + k⦄ := by
  vcgen simp [Nat.zero_add]
  trace_state
  all_goals sorry
