open nat tactic
universe variables u variables {A : Type u}

attribute [simp]
definition succ_eq_add (n : nat) : succ n = n + 1 :=
rfl

example (n m : nat) (H : succ (succ n) = succ m) : true :=
by do H  ← get_local `H,
      t  ← infer_type H,
      s  ← simp_lemmas.mk_default,
      t' ← s^.rsimplify t,
      trace t',
      exact (expr.const `trivial [])
