universe variables u

def ex (p q : nat → nat → Prop) (h : ∃ x, p x x ∧ q x x) : ∃ x y, p x y :=
begin [smt]
  by_contra,
  destruct h,
  smt_tactic.add_lemmas_from_facts,
  ematch
end

#print ex

lemma ex2 (p q : nat → nat → Prop) (h : ∃ x, p x x ∧ q x x) : ∃ x, p x x :=
begin [smt]
  by_contra,
  destruct h,
  smt_tactic.add_lemmas_from_facts,
  ematch
end
