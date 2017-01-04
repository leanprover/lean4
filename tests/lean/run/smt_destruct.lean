open smt_tactic

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
by using_smt $ do
   trace_state,
   a_1 ← tactic.get_local `a_1,
   destruct a_1,
   repeat close

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt]
   assert h : p ∨ q,
   destruct h
end

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt]
   destruct a_1 -- bad style, it relies on automatically generated names
end

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt] -- the default configuration is classical
   by_cases p
end

example (p q : Prop) [decidable p] : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt] with default_smt_config^.set_classical ff,
   by_cases p -- will fail if p is not decidable
end

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] -- the default configuration is classical
  by_contradiction,
  trace_state,
  by_cases p,
end

example (p q : Prop) [decidable p] : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] with default_smt_config^.set_classical ff,
   by_cases p -- will fail if p is not decidable
end

example (p q : Prop) [decidable p] [decidable q] : p ∨ q → p ∨ ¬q → ¬p ∨ q → p ∧ q :=
begin [smt] with default_smt_config^.set_classical ff,
   by_contradiction, -- will fail if p or q is not decidable
   trace_state,
   by_cases p -- will fail if p is not decidable
end
