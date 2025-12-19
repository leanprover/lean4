-- this benchmark exercises basic proof-engine operations through `apply` and `intros

set_option maxRecDepth 10000

macro "gen_term" n:num : term => do
  let mut stx ← `(True)
  for _ in 0...n.getNat do
    stx := ← `(let z : Nat := x + y; forall x : Nat, exists y : Nat, y = z+x /\ $stx)
  `(let z : Nat := 0 ; forall x : Nat, exists y : Nat, y = z+x ∧ $stx)

example : gen_term 500 := by
  repeat (intros; apply Exists.intro; apply And.intro; try apply rfl); try apply True.intro
