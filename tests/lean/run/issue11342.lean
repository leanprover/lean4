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
  failed to generate equality theorem _private.lean.run.issue11342.0.natToBin3.match_1.congr_eq_2 for `match` expression `natToBin3.match_1`
  case else.even
  motive✝ : (x : Nat) → Parity x → Sort u_1
  h_1✝ : (x : Parity 0) → motive✝ 0 x
  h_2✝ : (j : Nat) → motive✝ (j + j) (Parity.even j)
  h_3✝ : (j : Nat) → motive✝ (j + j).succ (Parity.odd j)
  j✝ n✝ : Nat
  h✝ : Nat.hasNotBit 1 (n✝ + n✝).ctorIdx
  heq_1✝ : n✝ + n✝ = j✝ + j✝
  heq_2✝ : Parity.even n✝ ≍ Parity.even j✝
  x✝ : ∀ (x : Parity 0), n✝ + n✝ = 0 → Parity.even n✝ ≍ x → False
  ⊢ h_2✝ n✝ ≍ h_2✝ j✝
---
error: Unknown constant `natToBin3.match_1.congr_eq_1`
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.congr_eq_1
