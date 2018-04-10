namespace tactic.interactive

meta def smt (tac : smt_tactic.interactive.itactic) : tactic unit :=
solve1 $ using_smt $ tac

end tactic.interactive

def f (a : nat) := a

example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : f b = c + 0 :=
begin
  smt { trace_state, change f b = c, add_lhs_lemma f.equations._eqn_1, ematch }
end
