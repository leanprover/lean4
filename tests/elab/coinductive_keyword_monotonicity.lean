/-!
Tests for the `monotonicity_by` clause on the `coinductive` and `inductive` keywords, which provides
an explicit monotonicity proof for the underlying lattice-theoretic fixpoint construction,
analogously to `coinductive_fixpoint monotonicity ...` / `inductive_fixpoint monotonicity ...`.
-/

open Lean.Order

section
variable (α : Type)

-- Explicit tactic proof on a plain coinductive predicate

coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a
monotonicity_by repeat monotonicity

/--
info: infSeq.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq α r b → infSeq α r a
-/
#guard_msgs in
#check infSeq.step

/--
info: infSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) (hyp : ∀ (a : α), pred a → ∃ b, r a b ∧ pred b)
  (a✝ : α) : pred a✝ → infSeq α r a✝
-/
#guard_msgs in
#check infSeq.coinduct

-- Term-style proof with `sorry` still produces the predicate and its constructors

/--
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
coinductive infSeq' (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq' r b → infSeq' r a
monotonicity_by sorry

/--
info: infSeq'.step (α : Type) (r : α → α → Prop) {a b : α} : r a b → infSeq' α r b → infSeq' α r a
-/
#guard_msgs in
#check infSeq'.step

-- The goal the explicit proof is elaborated against

/--
trace: α✝ α : Type
r : α → α → Prop
⊢ monotone fun f a => ∃ b, r a b ∧ f b
---
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
coinductive infSeq'' (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq'' r b → infSeq'' r a
monotonicity_by trace_state; sorry

end

-- Type errors in the provided proof are reported at the term

/--
error: Type mismatch
  ()
has type
  Unit
of sort `Type` but is expected to have type
  monotone fun f => ¬f
of sort `Prop`
---
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
coinductive selfNeg : Prop where
  | mk : ¬selfNeg → selfNeg
monotonicity_by exact ()

-- Mutual clique of two coinductive predicates, clause on only one member

mutual
  coinductive tick : Prop where
    | mk : tock → tick
  monotonicity_by repeat monotonicity

  coinductive tock : Prop where
    | mk : tick → tock
end

/-- info: tick.mk : tock → tick -/
#guard_msgs in
#check tick.mk

-- Mixed `inductive`/`coinductive` clique with a clause on each member

mutual
  coinductive ping : Prop where
    | mk : ¬pong → ping
  monotonicity_by repeat monotonicity

  inductive pong : Prop where
    | mk : ¬ping → pong
  monotonicity_by repeat monotonicity
end

/-- info: ping.mk : ¬pong → ping -/
#guard_msgs in
#check ping.mk

/-- info: pong.mk : ¬ping → pong -/
#guard_msgs in
#check pong.mk

-- The clause is rejected on ordinary inductive types

/--
error: `monotonicity_by` is only allowed on `coinductive` predicates, or on `inductive` predicates in a `mutual` block together with a `coinductive` predicate
-/
#guard_msgs in
inductive Plain : Prop where
  | mk : Plain
monotonicity_by repeat monotonicity

/--
error: `monotonicity_by` is only allowed on `coinductive` predicates, or on `inductive` predicates in a `mutual` block together with a `coinductive` predicate
-/
#guard_msgs in
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  monotonicity_by repeat monotonicity

  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
