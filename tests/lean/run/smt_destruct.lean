open smt_tactic

lemma ex1 (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
by using_smt $ do
   intros,
   trace_state,
   a_1 ← tactic.get_local `a_1,
   destruct a_1,
   iterate close

lemma ex2 (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt]
   intros,
   have h : p ∨ q,
   destruct h
end

lemma ex3 (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt]
   intros,
   destruct a_1 -- bad style, it relies on automatically generated names
end

lemma ex4 (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt] -- the default configuration is classical
   intros,
   by_cases p
end

lemma ex5 (p q : Prop) [decidable p] : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt] with {smt_config .}^.set_classical ff,
   intros,
   by_cases p -- will fail if p is not decidable
end

lemma ex6 (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] -- the default configuration is classical
  intros,
  by_contradiction,
  trace_state,
  by_cases p,
end

lemma ex7 (p q : Prop) [decidable p] : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] with {smt_config .}^.set_classical ff,
   intros,
   by_cases p -- will fail if p is not decidable
end

lemma ex8 (p q : Prop) [decidable p] [decidable q] : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] with {smt_config .}^.set_classical ff,
   intros,
   by_contradiction, -- will fail if p or q is not decidable
   trace_state,
   by_cases p -- will fail if p is not decidable
end
