-- Coinductive predicate definition
def infseq {α} (R : α → α → Prop) : α → Prop :=
  λ x : α => ∃ y, R x y ∧ infseq R y
  greatest_fixpoint

-- Application of the rewrite rule
def infseq_fixpoint {α} (R : α → α → Prop) (x : α) :
  infseq R x = ∃ y, R x y ∧ infseq R y := by
    rw [infseq]

-- The associated coinduction principle
theorem infseq.coind {α} (h : α → Prop) (R : α → α → Prop)
  (prem : ∀ (x : α), h x → ∃ y, R x y ∧ h y) : ∀ x, h x → infseq R x := by
  apply infseq.fixpoint_induct
  exact prem
/--
info: infseq.fixpoint_induct.{u_1} {α : Sort u_1} (R : α → α → Prop) (x : α → Prop)
  (y : ∀ (x_1 : α), x x_1 → ∃ y, R x_1 y ∧ x y) (x✝ : α) : x x✝ → infseq R x✝
-/
#guard_msgs in #check infseq.fixpoint_induct

-- Simple proof by coinduction
theorem cycle_infseq {R : α → α → Prop} (x : α) : R x x → infseq R x := by
  apply @infseq.fixpoint_induct α R (λ m => R m m)
  intro x _
  apply Exists.intro x
  trivial

-- Inductive predicate, as a inductive definition
inductive star (R : α → α → Prop) : α → α → Prop where
  | star_refl : ∀ x : α, star R x x
  | star_step : ∀ x y z, R x y → star R y z → star R x z

-- Inductive predicate, as a least fixpoint
def star_ind (tr : α → α → Prop) (q₁ q₂ : α) : Prop :=
 ∃ (z : α), q₁ = q₂ ∨ (tr q₁ z ∧ star_ind tr z q₂)
least_fixpoint

/--
info: star_ind.fixpoint_induct.{u_1} {α : Sort u_1} (tr : α → α → Prop) (q₂ : α) (x : α → Prop)
  (y : ∀ (x_1 : α), (∃ z, x_1 = q₂ ∨ tr x_1 z ∧ x z) → x x_1) (x✝ : α) : (fun q₁ => star_ind tr q₁ q₂) x✝ → x x✝
-/
#guard_msgs in #check star_ind.fixpoint_induct

-- From one you can prove the other
theorem star_implies_star' (R : α → α → Prop) : ∀ a b : α, star R a b → star_ind R a b := by
  intro a b s
  induction s
  case star_refl x =>
    unfold star_ind
    apply Exists.intro x
    left
    trivial
  case star_step x y z rel s2 ih =>
    unfold star_ind
    apply Exists.intro y
    right
    trivial

-- More elaborate example from Xavier Leroy's compiler verification course
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
    apply @infseq.fixpoint_induct _ _ (fun a => ∃ b, star R a b ∧ X b)
    case x =>
      apply Exists.elim (h₁ a rel)
      intro a' ⟨h₁, h₂⟩
      apply Exists.intro a'
      apply And.intro
      apply plus_star
      exact h₁
      exact h₂
    case y =>
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

-- Automata theory example that involves forall quantifier
def DFA (Q : Type) (A : Type) : Type := Q → (Bool × (A → Q))

def language_equivalent (automaton : DFA Q A) (q₁ q₂ : Q)  : Prop :=
  let ⟨o₁, t₁⟩ := automaton q₁
  let ⟨o₂, t₂⟩ := automaton q₂
  o₁ = o₂ ∧ (∀ a : A, language_equivalent automaton (t₁ a) (t₂ a))
greatest_fixpoint

/--
info: language_equivalent.fixpoint_induct {Q A : Type} (automaton : DFA Q A) (x : Q → Q → Prop)
  (y :
    ∀ (x_1 x_2 : Q),
      x x_1 x_2 →
        (automaton x_1).fst = (automaton x_2).fst ∧ ∀ (a : A), x ((automaton x_1).snd a) ((automaton x_2).snd a))
  (x✝ x✝¹ : Q) : x x✝ x✝¹ → language_equivalent automaton x✝ x✝¹
-/
#guard_msgs in
#check language_equivalent.fixpoint_induct

namespace mixed1
  mutual
    def tick : Prop :=
      ¬tock
    greatest_fixpoint

    def tock : Prop :=
      ¬tick
    least_fixpoint
  end
end mixed1

namespace mixed2
  mutual
    def tick : Prop :=
      ¬tock
    greatest_fixpoint

    def tock : Prop :=
      ¬tick
    least_fixpoint
  end
end mixed2

namespace mixed3
  mutual
    def tick : Prop :=
      tock → tick
    greatest_fixpoint

    def tock : Prop :=
      tick → tock
    least_fixpoint
  end
end mixed3

namespace mixed4
  mutual
    def tick : Prop :=
      tock → tick
    least_fixpoint

    def tock : Prop :=
      tick → tock
    greatest_fixpoint
  end
end mixed4
