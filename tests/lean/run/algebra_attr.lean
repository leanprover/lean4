def f (a b : nat) := 0
def g (a b : nat) := 1

instance : is_commutative nat f :=
⟨λ a b, rfl⟩

instance : is_commutative nat g :=
⟨λ a b, rfl⟩

open tactic

run_cmd do
 env ← get_env,
 s   ← return $ env.get_class_attribute_symbols `algebra,
 trace s
