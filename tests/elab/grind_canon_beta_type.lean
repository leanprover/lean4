set_option trace.grind.assert true
set_option pp.explicit true

-- The `((fun X ↦ Fin (X.size + 1)) (Vector.singleton 1))` must be canonicalized to `Fin 2`.
/--
trace: [grind.assert] Not
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) i
        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 1))))
[grind.assert] Not
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) i
        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 0))))
-/
#guard_msgs in
example (i : Fin 2)
    (h : i ≠ (@OfNat.ofNat ((fun X ↦ Fin (X.size + 1)) (Vector.singleton 1)) (nat_lit 1) _)) :
    i = 0 := by
  grind
