#check (⟨1, 2⟩ : nat × nat)

#check (⟨trivial, trivial⟩ : true ∧ true)

example : true := sorry

#check (⟨1, sorry⟩ : Σ' x : nat, x > 0)

open tactic

#check show true, from ⟨⟩

#check (⟨1, by intro1 >> contradiction⟩ : ∃ x : nat, 1 ≠ 0)
universe variables u v
#check λ (A B C : Prop),
  assume (Ha : A) (Hb : B) (Hc : C),
  show B ∧ A, from
  ⟨Hb, Ha⟩

#check λ (A B C : Prop),
  assume (Ha : A) (Hb : B) (Hc : C),
  show B ∧ A ∧ C ∧ A, from
  ⟨Hb, ⟨Ha, ⟨Hc, Ha⟩⟩⟩

#check λ (A B C : Prop),
  assume (Ha : A) (Hb : B) (Hc : C),
  show B ∧ A ∧ C ∧ A, from
  ⟨Hb, Ha, Hc, Ha⟩

#check λ (A B C : Prop),
  assume (Ha : A) (Hb : B) (Hc : C),
  show ((B ∧ true) ∧ A) ∧ (C ∧ A), from
  ⟨⟨⟨Hb, ⟨⟩⟩, Ha⟩, ⟨Hc, Ha⟩⟩

#check λ (A : Type u) (P : A → Prop) (Q : A → Prop),
  take (a : A), assume (H1 : P a) (H2 : Q a),
  show ∃ x, P x ∧ Q x, from
  ⟨a, ⟨H1, H2⟩⟩

#check λ (A : Type u) (P : A → Prop) (Q : A → Prop),
  take (a : A) (b : A), assume (H1 : P a) (H2 : Q b),
  show ∃ x y, P x ∧ Q y, from
  ⟨a, ⟨b, ⟨H1, H2⟩⟩⟩

#check λ (A : Type u) (P : A → Prop) (Q : A → Prop),
  take (a : A) (b : A), assume (H1 : P a) (H2 : Q b),
  show ∃ x y, P x ∧ Q y, from
  ⟨a, b, H1, H2⟩
