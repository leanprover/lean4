definition Sum : nat → (nat → nat) → nat := sorry
attribute [forward]
definition Sum_weird (f g h : nat → nat) (n : nat) : (Sum n (λ x, f (g (h x)))) = 1 := sorry
print Sum_weird

/-
attribute [forward]
definition Sum_weird : ∀ (f g h : nat → nat) (n : nat), eq (Sum n (λ (x : nat), f (g (h x)))) 1 :=
λ (f g h : nat → nat) (n : nat), sorry
(multi-)patterns:
?M_1 : nat → nat, ?M_2 : nat → nat, ?M_3 : nat → nat, ?M_4 : nat
{Sum ?M_4 (λ (x : nat), ?M_1)}
-/
