set_option pp::implicit true
check let P :  Nat → Bool    := λ x, x ≠ 0,
          Q :  ∀ x, P (x + 1) := λ x, Nat::succ_nz x
      in  Q