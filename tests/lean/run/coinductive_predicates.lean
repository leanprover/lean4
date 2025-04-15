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

theorem star_one (R : α → α → Prop)  : ∀ a b : α, R a b → star R a b := by
  intros a b Rab
  apply star.star_step
  exact Rab
  apply star.star_refl

theorem star_trans {α} (R : α → α → Prop) : ∀ (a b : α), star R a b → ∀ c : α, star R b c → star R a c := by
  intros a b sab
  intro c
  intro sbc
  induction sab
  case star_refl => exact sbc
  case star_step rel m ih =>
    apply star.star_step
    exact rel
    apply ih
    trivial

inductive plus (R : α → α → Prop) : α → α → Prop where
| plus_left : ∀ a b c, R a b → star R b c → plus R a c

theorem plus_one : ∀ a b, R a b → plus R a b := by
  intro a b Rab
  apply plus.plus_left
  exact Rab
  apply star.star_refl

theorem plus_star : ∀ a b, plus R a b → star R a b := by
    intro a b h
    cases h
    case plus_left h₁ h₂ h₃ =>
      apply star.star_step
      exact h₂
      exact h₃

theorem plus_star_trans (R : α → α → Prop)  : ∀ (a b c : α), star R a b → plus R b c → plus R a c := by
  intro a b c s p
  induction s
  case star_refl d =>
    exact p
  case star_step d e f rel s2 ih =>
    apply plus.plus_left
    exact rel
    apply plus_star
    apply ih
    exact p

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

theorem infseq_coinduction_principle_2:
  ∀ (x : α → Prop),
  (∀ (a : α), x a → ∃ b, plus R a b ∧ x b) →
  ∀ (a : α), x a → infseq R a := by
    intro X
    intro h₁ a rel
    apply infseq.coind (fun a => ∃ b, star R a b ∧ X b)
    case a =>
      apply Exists.elim (h₁ a rel)
      intro a' ⟨h₁, h₂⟩
      apply Exists.intro a'
      apply And.intro
      apply plus_star
      exact h₁
      exact h₂
    case prem =>
      intro a0 h₂
      apply Exists.elim h₂
      intro a1 ⟨ h₃ , h₄ ⟩
      have h₁' := h₁ a1 h₄
      apply Exists.elim h₁'
      intro mid ⟨ h₅, h₆⟩
      have t := plus_star_trans R a0 a1 mid h₃ h₅
      cases t
      case plus_left mid2 rel2 s =>
        apply Exists.intro mid2
        apply And.intro
        exact rel2
        apply Exists.intro mid
        exact ⟨ s, h₆ ⟩
