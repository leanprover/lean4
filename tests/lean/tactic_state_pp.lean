universe variables u

inductive Vec (α : Type u) : nat → Type u
| nil  : Vec 0
| cons : ∀ {n}, α → Vec n → Vec (nat.succ n)

constant f {α : Type u} {n : nat} : Vec α n → nat
axiom fax1 (α : Type u) : f (Vec.nil α) = 0
axiom fax2 {α : Type u} {n : nat} (v : Vec α (nat.succ n)) : f v = 1

open tactic
meta def pp_state_core : tactic format :=
do t     ← target,
   t_fmt ← pp t,
   return $ to_fmt "Goal: " ++ t_fmt

meta def pp_state (s : tactic_state) : format :=
match pp_state_core s with
| tactic_result.success r _             := r
| tactic_result.exception .format _ _ _ := "failed to pretty print"
end

meta instance i2 : has_to_format tactic_state :=
⟨λ s, to_fmt "My custom goal visualizer" ++ format.line ++ pp_state s⟩

example {α : Type u} {n : nat} (v : Vec α n) : f v ≠ 2 :=
begin
  destruct v,
  intros, intro, note h := fax1 α, cc,
  -- intros n1 h t, intros, intro, note h := fax2 (Vec.cons h t), cc
end

open nat
example : ∀ n, 0 < n → succ (pred n) = n :=
begin
  intro n,
  destruct n,
   dsimp, intros, note h := lt_irrefl 0, cc,
end
