import tactic

-- Create a simple rewrite set
rewrite_set simple
add_rewrite Nat::add_zeror Nat::add_zerol Nat::add_comm eq_id : simple

-- Prove the following theorem using the simplifier with the rewrite set simple
theorem Test (a b : Nat) : 0 + a + 0 + b = b + a := (by simp simple)
