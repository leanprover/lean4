open tactic nat expr option

attribute [simp]
lemma succ_eq_add (n : nat) : succ n = n + 0 + 1 :=
rfl

example (a b : nat) : a = b → succ (succ a) = succ (b + 1) :=
by do intro `Heq,
      get_local `a >>= subst,
      trace_state,
      dsimp,
      trace "---- after dsimp ----",
      trace_state,
      t ← target,
      match (is_eq t) with
      | (some (lhs, rhs)) := do pr ← mk_app `eq.refl [lhs], exact pr
      | none              := failed
      end
