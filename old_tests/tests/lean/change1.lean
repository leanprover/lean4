open tactic nat expr option

attribute [simp]
lemma succ_eq_add (n : nat) : succ n = n + 1 :=
rfl

example (a b : nat) : a = b → succ (succ a) = succ (b + 1) :=
by do intro `Heq,
      trace_state,
      s ← simp_lemmas.mk_default,
      t' ← target >>= s^.dsimplify,
      change t',
      trace "---- after change ----",
      trace_state,
      get_local `a >>= subst,
      t ← target,
      match (is_eq t) with
      | (some (lhs, rhs)) := do pr ← mk_app `eq.refl [lhs], exact pr
      | none              := failed
      end
