import Lean.Elab.Command
import Lean.Meta.Match.MatchEqsExt

def test1 : Nat → Nat
  | 0 => 0
  | _+1 => 42

-- set_option pp.match false

/--
info: test1.match_1.lifter.{u, v} {α : Sort u} {β : Sort v} (f : α → β) (x✝ : Nat) (h_1 : Unit → (fun x => α) 0)
  (h_2 : (n : Nat) → (fun x => α) n.succ) :
  f
      (match x✝ with
      | 0 => h_1 ()
      | n.succ => h_2 n) =
    match x✝ with
    | 0 => f (h_1 ())
    | n.succ => f (h_2 n)
-/
#guard_msgs in
#check test1.match_1.lifter

def test2 (α β) : α ∨ β → γ → (β ∨ α) ∧ γ
  | .inl x, y => ⟨.inr x, y⟩
  | .inr x, y => ⟨.inl x, y⟩

set_option pp.proofs true in
/--
info: test2.match_1.lifter {α β : Prop} (f : α → β) {γ : Prop} (α✝ β✝ : Prop) (x✝ : α✝ ∨ β✝) (x✝¹ : γ)
  (h_1 : ∀ (x : α✝) (y : γ), (fun x x => α) (Or.inl x) y) (h_2 : ∀ (x : β✝) (y : γ), (fun x x => α) (Or.inr x) y) :
  f
      (match x✝, x✝¹ with
      | Or.inl x, y => h_1 x y
      | Or.inr x, y => h_2 x y) =
    match x✝, x✝¹ with
    | Or.inl x, y => f (h_1 x y)
    | Or.inr x, y => f (h_2 x y)
-/
#guard_msgs in
#check test2.match_1.lifter

-- This fails if there is no splitter theorem for a match

/--
error: Failed to realize constant Nat.lt_or_gt_of_ne.match_1.lifter:
  Cannot construct match lifter:
    Could not construct splitter for Nat.lt_or_gt_of_ne.match_1
---
error: Failed to realize constant Nat.lt_or_gt_of_ne.match_1.lifter:
  Cannot construct match lifter:
    Could not construct splitter for Nat.lt_or_gt_of_ne.match_1
---
error: unknown identifier 'Nat.lt_or_gt_of_ne.match_1.lifter'
-/
#guard_msgs in
#check Nat.lt_or_gt_of_ne.match_1.lifter

-- A typical example

theorem List.filter_map' (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l <;> simp [filter, *, liftMatch]

-- Using the lift_match conv tactic

theorem List.filter_map'' (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l
  · simp
  · simp only [filter]
    conv => rhs; lift_match
    simp only [Function.comp_apply, map_cons, *]

-- Using the lift_match tactic

-- This works in principle, but isn't very useful, because the simplifier, even with
-- `(contextual := true)`, does not simplify the duplicated match target in the alternatives.
-- Looks like that would require congruence theorems for matchers.

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem List.filter_map''' (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l
  · simp
  · simp only [filter]
    lift_match
    simp (config := {contextual := true}) [*]
    -- fail
    sorry


-- A simple example

example (o : Option Bool) :
  (match o with | some b => b | none => false)
    = !(match o with | some b => !b | none => true) := by
  simp [liftMatch]

-- Can float out of ite-condition
/--
error: tactic 'fail' failed
o : Option Bool
P : Nat → Prop
⊢ P
    (match o with
    | some b => if b = true then 1 else 2
    | none => if True then 1 else 2)
-/
#guard_msgs in
example (o : Option Bool) (P : Nat → Prop):
  P (if (match o with | some b => b | none => true) then 1 else 2) := by
  simp only [liftMatch]
  fail

-- Cannot lift out of ite-branch
example (b : Bool) (o : Option Bool) (P : Bool → Prop) (abort : ∀ b, P b):
  P (if b then (match o with | some b => b | none => true) else b) := by
  fail_if_success simp only [liftMatch]
  apply abort

-- Can float out of a match target (aka case-of-case)
/--
error: tactic 'fail' failed
o : Option Bool
P : Nat → Prop
⊢ P
    (match o with
    | some b =>
      match b with
      | true => 1
      | false => 2
    | none => 1)
-/
#guard_msgs in
example (o : Option Bool) (P : Nat → Prop):
  P (match (match o with | some b => b | none => true) with | true => 1 | false => 2) := by
  simp only [liftMatch]
  fail

-- Dependent motive; must not rewrite

set_option trace.lift_match true in
/-- info: [lift_match] Cannot lift match: motive depends on targets -/
#guard_msgs in
example (o : Option Bool) (motive : Bool → Type) (P : {b : Bool} → motive b → Prop)
  (f : (x : Bool) → motive x) (g : {x : Bool} → motive x → motive x)
  (abort : ∀ b (x : motive b), P x) :
  P (g (match (motive := ∀ b, motive b.isSome) o with | some _ => f true | none => f false)) := by
  fail_if_success simp [liftMatch]
  apply abort

-- Dependent context; must not rewrite

set_option trace.lift_match true in
/-- info: [lift_match] Cannot lift match: f is dependent -/
#guard_msgs in
example (o : Option Bool) (motive : Bool → Type) (P : {b : Bool} → motive b → Prop)
  (f : (x : Bool) → motive x)
  (abort : ∀ b (x : motive b), P x) :
  P (f (match (motive := ∀ _, Bool) o with | some b => b | none => false)) := by
  fail_if_success simp [liftMatch]
  apply abort

-- Context depends on the concrete value of the match, must not rewrite

set_option trace.lift_match true in
/-- info: [lift_match] Cannot lift match: context is not type correct -/
#guard_msgs in
example (o : Option Bool)
  (f : (x : Bool) → (h : x = (match o with | some b => b | none => false)) → Bool)
  (abort : ∀ (P : Prop), P) :
  f (match (motive := ∀ _, Bool) o with | some b => b | none => false) rfl = true := by
  fail_if_success simp [liftMatch]
  apply abort

-- Can float out of a let (Only relevant with zeta := false)

/--
error: tactic 'fail' failed
o : Option Bool
P : Bool → Prop
⊢ P
    (match o with
    | some b =>
      let b := b;
      !b
    | none =>
      let b := true;
      !b)
-/
#guard_msgs in
example (o : Option Bool) (P : Bool → Prop):
  P (let b := match o with | some b => b | none => true; !b) := by
  simp -zeta only [liftMatch]
  fail

/-
This following code tries to create all float theorems for all matches found in the environment.
-/

-- At the time of writing, the following two quite large matches fail by running out of heartbeat
-- #check Lean.Expr.name?.match_1.float
-- #check Lean.Meta.reduceNat?.match_1.float

/-
open Lean Meta in
run_meta do
  for es in (Match.Extension.extension.toEnvExtension.getState (← getEnv)).importedEntries do
    for e in es do
      -- Let's not look at matchers that eliminate to Prop only
      if e.info.uElimPos?.isNone then continue
      withCurrHeartbeats do
        tryCatchRuntimeEx do
          let hasSplitter ← try
              discard <| Lean.Meta.Match.getEquationsFor e.name
              pure true
            catch _ => pure false
          if hasSplitter then
            let floatName := e.name ++ `float
            unless (← hasConst floatName) do
              executeReservedNameAction floatName
         fun ex =>
          logInfo m!"Failed to handle {e.name}:{ex.toMessageData}"
-/

-- Testing if-then-else

/--
error: tactic 'fail' failed
P : Nat → Prop
f : Nat → Nat
b : Bool
⊢ P (if b = true then f 1 else f 2)
-/
#guard_msgs in
example (P : Nat → Prop) (f : Nat → Nat) (b : Bool) :
  P (f (if b then 1 else 2)) := by
  simp only [liftMatch]
  fail

-- Dependent f

/--
error: simp made no progress
---
info: [lift_match] Cannot lift match: f is dependent
-/
#guard_msgs in
set_option trace.lift_match true in
example (P : {n : Nat} → Fin n → Prop) (f : (n : Nat) → Fin n) (b : Bool) :
  P (f (if b then 1 else 2)) := by
  simp only [liftMatch]
  fail

-- Somewhat dependent f, but abstracting still succeeds

/--
error: tactic 'fail' failed
P : Nat → Prop
f : (n : Nat) → DecidableEq (Fin n) → Nat
b : Bool
⊢ P (if b = true then f 1 inferInstance else f 2 inferInstance)
-/
#guard_msgs in
example (P : Nat → Prop) (f : (n : Nat) → DecidableEq (Fin n) → Nat) (b : Bool) :
  P (f (if b then 1 else 2) inferInstance) := by
  simp only [liftMatch]
  fail

-- Testing dependent if-then-else

/--
error: tactic 'fail' failed
P : Nat → Prop
f : Nat → Nat
b : Bool
⊢ P (if h : b = true then f 1 else f 2)
-/
#guard_msgs in
example (P : Nat → Prop) (f : Nat → Nat) (b : Bool) :
  P (f (if h : b then 1 else 2)) := by
  simp only [liftMatch]
  fail

-- Dependent f

/--
error: simp made no progress
---
info: [lift_match] Cannot lift match: f is dependent
-/
#guard_msgs in
set_option trace.lift_match true in
example (P : {n : Nat} → Fin n → Prop) (f : (n : Nat) → Fin n) (b : Bool) :
  P (f (if h : b then 1 else 2)) := by
  simp only [liftMatch]
  fail

-- Somewhat dependent f, but abstracting still succeeds

/--
error: tactic 'fail' failed
P : Nat → Prop
f : (n : Nat) → DecidableEq (Fin n) → Nat
b : Bool
⊢ P (if h : b = true then f 1 inferInstance else f 2 inferInstance)
-/
#guard_msgs in
example (P : Nat → Prop) (f : (n : Nat) → DecidableEq (Fin n) → Nat) (b : Bool) :
  P (f (if h : b then 1 else 2) inferInstance) := by
  simp only [liftMatch]
  fail
