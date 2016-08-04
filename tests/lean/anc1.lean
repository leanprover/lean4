check (⟨1, 2⟩ : nat × nat)

check (⟨trivial, trivial⟩ : true ∧ true)

example : true := sorry

check (⟨1, sorry⟩ : Σ x : nat, x > 0)

open tactic

check show true, from ⟨⟩

check (⟨1, by intro1 >> contradiction⟩ : ∃ x : nat, 1 ≠ 0)

check λ (A B C : Prop),
  assume (Ha : A) (Hb : B) (Hc : C),
  show B ∧ A, from
  ⟨Hb, Ha⟩
