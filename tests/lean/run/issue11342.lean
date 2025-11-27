inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

set_option trace.Meta.Match.matchEqs true

partial def natToBin3 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

-- #guard_msgs in
-- #print sig natToBin3.match_1.splitter

/--
error: Failed to realize constant natToBin3.match_1.congr_eq_1:
  right-hand side is not application of a free variables:
    case zero.h
    motive✝ : (x : Nat) → Parity x → Sort u_1
    h_1✝ : (x : Parity 0) → motive✝ 0 x
    h_2✝ : (j : Nat) → motive✝ (j + j) (Parity.even j)
    h_3✝ : (j : Nat) → motive✝ (j + j).succ (Parity.odd j)
    x✝ : Parity 0
    heq_1✝ : Nat.zero = 0
    ⊢ natToBin3._sparseCasesOn_1 (motive := fun x => (x_1 : Parity x) → motive✝ x x_1) Nat.zero (fun x => h_1✝ x)
          (fun h x =>
            Parity.casesOn (motive := fun a x_1 => Nat.zero = a → x ≍ x_1 → motive✝ Nat.zero x) x
              (fun n h_1 =>
                Eq.ndrec (motive := fun x =>
                  Nat.hasNotBit 1 x.ctorIdx → (x_1 : Parity x) → x_1 ≍ Parity.even n → motive✝ x x_1)
                  (fun h x h_2 => ⋯ ▸ h_2✝ n) ⋯ h x)
              (fun n h_1 =>
                Eq.ndrec (motive := fun x =>
                  Nat.hasNotBit 1 x.ctorIdx → (x_1 : Parity x) → x_1 ≍ Parity.odd n → motive✝ x x_1)
                  (fun h x h_2 => ⋯ ▸ h_3✝ n) ⋯ h x)
              ⋯ ⋯)
          x✝ =
        h_1✝ x✝
---
error: Unknown constant `natToBin3.match_1.congr_eq_1`
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.congr_eq_1
