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

example (a b : int) : a + 0 = 0 + b → a = b :=
by do
  H ← intro "H",
  simp_at H,
  assumption

example (a b c : int) : a = 0 → a + b = c + a → b = c :=
by do
  H1 ← intro "H1",
  H2 ← intro "H2",
  simp_at_using_hs H2,
  assumption

constant p {a b : int} : a = b → Prop

example (a b : int) (f : int → int) (H : a = 0) (H₁ : a = b) (H₂ : p H₁) : 0 = b :=
by do
  get_local "H₁" >>= simp_at_using_hs,
  trace_state, -- H₁ is not replaced since it has dependencies
  get_local "H₁" >>= exact
