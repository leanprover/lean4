def infinite_chain {α} (step : α → Option α) (x : α) : Prop :=
  ∃ y, step x = some y ∧ (infinite_chain step y)
  greatest_fixpoint

def infinite_chain_fixpoint {α} (step : α → Option α) (x : α) :
  infinite_chain step x = ∃ y, step x = some y ∧ infinite_chain step y := by
    rw [infinite_chain]

#check infinite_chain.fixpoint_induct

theorem infinite_chain.coind {α} (P : α → Prop) (step : α → Option α)
  (h : ∀ (x : α), P x → ∃ y, step x = some y ∧ P y) :
  ∀ x, P x → infinite_chain step x := infinite_chain.fixpoint_induct _ _ h

def stream (Q : Type) : Type := Q → Nat × Q

def stream_bisimilarity (Q : Type) (transition_function : stream Q) (q₁ q₂ : Q) : Prop :=
    (transition_function q₁).fst  = (transition_function q₂).fst
  ∧ stream_bisimilarity Q transition_function (transition_function q₁).snd (transition_function q₂).snd
greatest_fixpoint

#check stream_bisimilarity.fixpoint_induct
