/-!
When `Sym.simp` rewrites an argument that the class of a later instance argument depends on,
the instance is synthesized for the new class instead of being reused when it is definitionally
an instance of it: `decide (x ≤ 2 + 3)` becomes `@decide (x ≤ 5) (x.decLe 5)`, not
`@decide (x ≤ 5) (x.decLe (2 + 3))`. The definitional check also unified the old and new
arguments, which for `Int32.minValue + c` with a non-reducible `c` unfolds `Int32` addition
down to `Nat.add` and hits the recursion limit.
-/

set_option warn.sorry false

def c : Int32 := 5

set_option pp.explicit true in
/--
trace: x : Nat
⊢ @Eq Bool
    (@decide (@LE.le Nat instLENat x (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      (x.decLe (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
    false
-/
#guard_msgs in
example (x : Nat) : decide (x ≤ 2 + 3) = false := by grind_norm sym; trace_state; sorry

-- The example from `rc_model.lean`, reduced: the proposition is reordered under `decide`.
example (x : Int32) : decide (x ≤ Int32.minValue + c) = false := by
  grind_norm sym; guard_target =ₛ decide (x ≤ -2147483648 + c) = false; sorry

section sym
set_option backward.grind.normalizer false
set_option linter.unusedVariables false in
example (rc : Int32) (h : decide (rc ≤ Int32.minValue + c) = false) : rc = rc := by grind
example (rc : Int32) (h : decide (rc ≤ Int32.minValue + c) = false) : ¬ rc ≤ c + 2147483648 := by grind
end sym
