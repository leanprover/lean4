/-
Simulating classical reasoning without assuming excluded middle.
The idea is to use the double-negation translation.
We define several "helper" theorems for double negated formulas.
-/
variables {p q r : Prop}

theorem not_and_of_or_not : ¬p ∨ ¬q → ¬(p ∧ q) :=
λ h hpq, or.elim h
  (λ hnp : ¬p, absurd (and.elim_left hpq) hnp)
  (λ hnq : ¬q, absurd (and.elim_right hpq) hnq)

theorem not_or_elim_left : ¬(p ∨ q) → ¬p :=
λ hpq hp, absurd (or.inl hp) hpq

theorem not_or_elim_right : ¬(p ∨ q) → ¬q :=
λ hpq hq, absurd (or.inr hq) hpq

theorem not_imp_elim_right : ¬(p → q) → ¬q :=
λ h₁ hq, absurd (λ h, hq) h₁

theorem not_imp_elim_left : ¬(p → q) → ¬¬p :=
λ h₁ hnp, absurd (λ hp, by contradiction) h₁

theorem not_imp_intro : ¬¬p → ¬q → ¬(p → q) :=
λ hnnp hnq hpq,
  have hnp : ¬ p, from λ hp, absurd (hpq hp) hnq,
  absurd hnp hnnp

/- Double negation introduction -/
theorem nn_intro : p → ¬¬p :=
λ hp hnp, absurd hp hnp

/- Double negated implication -/
-- Introduction
theorem nn_imp_intro : (¬¬p → ¬¬q) → ¬¬(p → q) :=
λ h hnpq,
  have hnnp : ¬¬p, from not_imp_elim_left hnpq,
  have hnq  : ¬q,  from not_imp_elim_right hnpq,
  have hnnq : ¬¬q, from h hnnp,
  absurd hnq hnnq

-- Elimination (modus ponens)
theorem nn_mp : ¬¬(p → q) → p → ¬¬q :=
λ hpq hp hnq,
  have aux : ¬(p → q), from not_imp_intro (nn_intro hp) hnq,
  absurd aux hpq

-- Double negated modus tollens
theorem nn_mt : ¬¬(p → q) → ¬q → ¬p :=
λ hpq hnq hp, absurd hnq (nn_mp hpq hp)

/- Double negated disjuction -/
lemma not_or_of_not_of_not : ¬p → ¬q → ¬(p ∨ q) :=
λ hnp hnq hpq, or.elim hpq (λ hp, absurd hp hnp) (λ hq, absurd hq hnq)

-- Elimination
theorem nn_or_elim : ¬¬(p ∨ q) → (p → ¬¬r) → (q → ¬¬r) → ¬¬r :=
λ hpq hpr hqr hnr,
  have hnp : ¬p, from λhp, absurd hnr (hpr hp),
  have hnq : ¬q, from λhq, absurd hnr (hqr hq),
  have aux : ¬(p ∨ q), from not_or_of_not_of_not hnp hnq,
  absurd aux hpq

-- Introduction
theorem nn_or_inl : ¬¬p → ¬¬(p ∨ q) :=
λ h hnpq, absurd (not_or_elim_left hnpq) h

theorem nn_or_inr : ¬¬q → ¬¬(p ∨ q) :=
λ h hnpq, absurd (not_or_elim_right hnpq) h

/- Double negated conjunction -/

-- Elimination
theorem nn_and_elim_left : ¬¬(p ∧ q) → ¬¬p :=
λ h hnp, absurd (not_and_of_or_not (or.inl hnp)) h

theorem nn_and_elim_right : ¬¬(p ∧ q) → ¬¬q :=
λ h hnq, absurd (not_and_of_or_not (or.inr hnq)) h

-- Introduction
theorem nn_and_intro : ¬¬p → ¬¬q → ¬¬(p ∧ q) :=
λ hnnp hnnq hnpq,
  have h₁ : ¬(p → ¬q), from not_imp_intro hnnp hnnq,
  have h₂ :  p → ¬q,   from λ hp hq, absurd (and.intro hp hq) hnpq,
  absurd h₂ h₁

/- Double negated excluded middle -/
theorem nn_em : ¬¬(p ∨ ¬p) :=
λ hn,
  have hnp : ¬p,   from not_or_elim_left hn,
  have hnnp : ¬¬p, from not_or_elim_right hn,
  absurd hnp hnnp

/- Examples: the following two examples are classically valid.
   We can "simulate" the classical proofs using double negation.
-/
example : ¬¬((p → q) → (¬p ∨ q)) :=
nn_imp_intro (λ h, nn_or_elim (@nn_em p)
  (λ hp  : p,
     have hnnq : ¬¬q, from nn_mp h hp,
     nn_or_inr hnnq)
  (λ hnp : ¬p, nn_intro (or.inl hnp)))

/- "Prove" Peirce's law -/
example : ¬¬(((p → q) → p) → p) :=
nn_imp_intro (λ h, nn_or_elim (@nn_em p)
  (λ hp  :  p, nn_intro hp)
  (λ hnp : ¬p,
    have h₁ : ¬(p → q), from nn_mt h hnp,
    have hnnp : ¬¬p,    from not_imp_elim_left h₁,
    absurd hnp hnnp))
