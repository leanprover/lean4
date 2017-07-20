run_cmd tactic.run_async (tactic.trace
  "trace message from a different task")

def {u} foo {α : Type u} {n : ℕ} : array α (0+n) → array α n :=
if n = 0 then
  λ v, cast (by async { simp }) v
else
  λ v, cast (by async { simp }) v

#print foo
