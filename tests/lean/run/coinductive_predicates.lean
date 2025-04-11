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

def infseq {α} (R : α → α → Prop) : α → Prop :=
  λ x : α => ∃ y, R x y ∧ infseq R y
  greatest_fixpoint

#check infseq.fixpoint_induct

theorem infseq.coind {α} (h : α → Prop) (R : α → α → Prop)
  (prem : ∀ (x : α), h x → ∃ y, R x y ∧ h y) : ∀ x, h x → infseq R x := by
  apply infseq.fixpoint_induct
  exact prem


#check infseq.fixpoint_induct

theorem cycle_infseq {R : α → α → Prop} (x : α) : R x x → infseq R x := by
  apply @infseq.fixpoint_induct α R (λ m => R m m)
  intro x _
  apply Exists.intro x
  trivial

inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ x y z, R x y → star R y z → star R x z

def all_seq_inf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, star R x y → ∃ z, R y z

def infseq_if_all_seq_inf (R : α → α → Prop) : ∀ x,  all_seq_inf R x → infseq R x := by
  apply infseq.fixpoint_induct
  intro x H
  unfold all_seq_inf at H
  have H' := H x (by simp [star.star_refl])
  apply Exists.elim H'
  intro y Rxy
  apply Exists.intro y
  apply And.intro
  exact Rxy
  unfold all_seq_inf
  intro y'
  intro Ryy'
  apply H y'
  apply star.star_step
  exact Rxy
  trivial


--   apply infseq.fixpoint_induct
--   intro x all_inf
--   apply Exists.intro x
--   sorry
