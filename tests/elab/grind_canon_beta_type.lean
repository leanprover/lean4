set_option trace.grind.assert true
set_option pp.explicit true

-- The `((fun X ↦ Fin (X.size + 1)) (Vector.singleton 1))` must be canonicalized to `Fin 2`.
-- Besides the two input facts, the `[grind hom]` engine asserts the diseq translations
-- (`Fin.val` level and fully evaluated) and the `Fin.isLt` range predicates.
/--
trace: [grind.assert] Not
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) i
        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 1))))
[grind.assert] Not
      (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) i
        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 0))))
[grind.assert] Not
      (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
[grind.assert] @LE.le Nat instLENat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
[grind.assert] Not
      (@Eq Nat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
[grind.assert] @LE.le Nat instLENat (@Fin.val (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
-/
#guard_msgs in
example (i : Fin 2)
    (h : i ≠ (@OfNat.ofNat ((fun X ↦ Fin (X.size + 1)) (Vector.singleton 1)) (nat_lit 1) _)) :
    i = 0 := by
  grind
