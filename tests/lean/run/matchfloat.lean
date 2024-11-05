import Lean.Elab.Command

def test1 : Nat → Nat
  | 0 => 0
  | _+1 => 42

-- set_option pp.match false

/--
info: test1.match_1.float.{u, v} {α : Sort u} {β : Sort v} (f : α → β) (x✝ : Nat) (h_1 : Unit → (fun x => α) 0)
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
#check test1.match_1.float

def test2 (α β) : α ∨ β → γ → (β ∨ α) ∧ γ
  | .inl x, y => ⟨.inr x, y⟩
  | .inr x, y => ⟨.inl x, y⟩

set_option pp.proofs true in
/--
info: test2.match_1.float {α β : Prop} (f : α → β) {γ : Prop} (α✝ β✝ : Prop) (x✝ : α✝ ∨ β✝) (x✝¹ : γ)
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
#check test2.match_1.float

-- This fails if there is no splitter theorem for a match

/--
error: Failed to realize constant Nat.lt_or_gt_of_ne.match_1.float:
  Cannot construct match floating theorem:
    Could not construct splitter for Nat.lt_or_gt_of_ne.match_1
---
error: Failed to realize constant Nat.lt_or_gt_of_ne.match_1.float:
  Cannot construct match floating theorem:
    Could not construct splitter for Nat.lt_or_gt_of_ne.match_1
---
error: unknown identifier 'Nat.lt_or_gt_of_ne.match_1.float'
-/
#guard_msgs in
#check Nat.lt_or_gt_of_ne.match_1.float

-- A typical example

theorem List.filter_map' (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  induction l <;> simp [filter, map, *, match_float]

-- A simple example

example (o : Option Bool) :
  (match o with | some b => b | none => false)
    = !(match o with | some b => !b | none => true) := by
  simp [match_float]

-- Demonstration that this should really be used as a post-simproc (which luckily is the default)

/--
error: tactic 'fail' failed
o : Option Bool
P : Bool → Prop
⊢ P
    (match o with
    | some b => !!!b
    | none => !!!true)
-/
#guard_msgs in
example (o : Option Bool) (P : Bool → Prop): P !!!(match o with | some b => b | none => true) := by
  simp (config := {singlePass := true}) only [↑ match_float]
  fail

/--
error: tactic 'fail' failed
o : Option Bool
P : Bool → Prop
⊢ P
    !!match o with
        | some b => !b
        | none => !true
-/
#guard_msgs in
example (o : Option Bool) (P : Bool → Prop): P !!!(match o with | some b => b | none => true) := by
  simp (config := {singlePass := true}) only [↓ match_float]
  fail

/--
error: tactic 'fail' failed
o : Option Bool
P : Bool → Prop
⊢ P
    (match o with
    | some b => !!!b
    | none => !!!true)
-/
#guard_msgs in
example (o : Option Bool) (P : Bool → Prop): P !!!(match o with | some b => b | none => true) := by
  simp (config := {singlePass := true}) only [match_float]
  fail

-- Can float out of ite-condition
set_option trace.match_float true in
example (o : Option Bool) (P : Nat → Prop):
  P (if (match o with | some b => b | none => true) then 1 else 2) := by
  simp only [match_float]
  fail

-- Cannot float out of ite-branch
example (b : Bool) (o : Option Bool) (P : Bool → Prop) (abort : ∀ b, P b):
  P (if b then (match o with | some b => b | none => true) else b) := by
  fail_if_success simp only [match_float]
  apply abort

-- Dependent context; must not rewrite

set_option trace.match_float true in
/-- info: [match_float] Cannot float match: f is dependent -/
#guard_msgs in
example (o : Option Bool) (motive : Bool → Type) (P : {b : Bool} → motive b → Prop)
  (f : (x : Bool) → motive x)
  (abort : ∀ b (x : motive b), P x) :
  P (f (match (motive := ∀ _, Bool) o with | some b => b | none => false)) := by
  fail_if_success simp [match_float]
  apply abort

-- Context depends on the concrete value of the match, must not rewrite

set_option trace.match_float true in
/-- info: [match_float] Cannot float match: context is not type correct -/
#guard_msgs in
example (o : Option Bool)
  (f : (x : Bool) → (h : x = (match o with | some b => b | none => false)) → Bool)
  (abort : ∀ (P : Prop), P) :
  f (match (motive := ∀ _, Bool) o with | some b => b | none => false) rfl = true := by
  fail_if_success simp [match_float]
  apply abort

/-
This code quickly finds many matcher where deriving the floater fails, usually
because the splitter cannot be generated, for example Nat.lt_or_gt_of_ne.match_1.float

open Lean Meta in
run_meta do
  for es in (Match.Extension.extension.toEnvExtension.getState (← getEnv)).importedEntries do
    for e in es do
      -- Let's not look at matchers that eliminate to Prop only
      if e.info.uElimPos?.isNone then continue
      let _ ← realizeGlobalName (e.name ++ `float)

-/
