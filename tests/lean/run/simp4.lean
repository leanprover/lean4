import algebra.ordered_ring
open tactic binary

constant int : Type₁

definition int_decidable_linear_ordered_comm_ring [instance] : decidable_linear_ordered_comm_ring int :=
sorry

attribute [simp] abs_neg abs_abs

example (a b c : int) : a = 0 → b = 0 → a + b + c = c :=
by intros >> simp_using_hs

example (f : int → int → int) (a b : int) : commutative f → f a (f a b) = f (f b a) a :=
by intros >> simp_using_hs

example (a b c : int) : 0 = c →
  c +
  abs (- abs (- abs (abs (abs (abs (abs a)))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs c)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b))))))))))
  =
  0 + 0 +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs 0)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (- a))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- abs (- abs (- abs (- abs (abs (abs (abs (abs (abs (abs b)))))))))) +
  abs (- b) +
  abs b :=
by do H ← intro "H",
      H1 ← mk_app ("eq" <.> "symm") [H],
      simp_using [H1]
