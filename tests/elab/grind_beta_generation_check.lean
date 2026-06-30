/-!
Support for beta-reduction in `grind` must respect generation threshold.
-/
set_option warn.sorry false

/--
trace: [grind.beta] f 0 = f 0, using fun b => f b
[grind.beta] f 0 = f (0 + 1), using fun b => f (b + 1)
[grind.beta] f 1 = f 1, using fun b => f b
[grind.beta] f 1 = f (1 + 1), using fun b => f (b + 1)
[grind.beta] f 2 = f 2, using fun b => f b
[grind.beta] f 2 = f (2 + 1), using fun b => f (b + 1)
[grind.beta] f 3 = f 3, using fun b => f b
[grind.beta] f 3 = f (3 + 1), using fun b => f (b + 1)
[grind.beta] f 4 = f 4, using fun b => f b
[grind.beta] f 4 = f (4 + 1), using fun b => f (b + 1)
[grind.beta] f 5 = f 5, using fun b => f b
[grind.beta] f 5 = f (5 + 1), using fun b => f (b + 1)
[grind.beta] f 6 = f 6, using fun b => f b
[grind.beta] f 6 = f (6 + 1), using fun b => f (b + 1)
-/
#guard_msgs (trace) in
set_option trace.grind.beta true in
protected theorem Multipliable.tprod_eq_zero_mul' {f : Nat → Nat} (h : (fun b => f (b + 1)) = fun b => f b) (a : Nat)
    (R : Nat → Nat → Prop) : R a (f 0) := by
  fail_if_success grind -ring -linarith -order -lia -ac (splits := 0) -verbose
  sorry
