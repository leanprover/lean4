import data.vector

run_cmd tactic.run_async (tactic.trace
  "trace message from a different task")

def {u} foo {α : Type u} {n : ℕ} : vector α (0+n) → vector α n :=
if n = 0 then
  λ v, cast (by async { simp }) v
else
  λ v, cast (by async { simp }) v

#print foo
