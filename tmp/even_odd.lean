import data.vector
open nat
universes u v

-- set_option trace.eqn_compiler.wf_rec true
-- set_option trace.debug.eqn_compiler.wf_rec true
-- set_option trace.debug.eqn_compiler.mutual true

mutual def even, odd
with even : nat → bool
| 0     := tt
| (a+1) := odd a
with odd : nat → bool
| 0     := ff
| (a+1) := even a

#eval even 3
#eval even 4
#eval odd 3
#eval odd 4
#check even.equations._eqn_1
#check even.equations._eqn_2
#check odd.equations._eqn_1
#check odd.equations._eqn_2

mutual def f, g {α β : Type u} (p : α × β)
with f : Π n : nat, vector (α × β) n
| 0        := vector.nil
| (succ n) := vector.cons p $ (g n p.1).map (λ b, (p.1, b))
with g : Π n : nat, α → vector β n
| 0        a := vector.nil
| (succ n) a := vector.cons p.2 $ (f n).map (λ p, p.2)

#check @f.equations._eqn_1
#check @f.equations._eqn_2
#check @g.equations._eqn_1
#check @g.equations._eqn_2
