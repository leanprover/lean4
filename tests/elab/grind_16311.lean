set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option linter.unusedVariables false

/-!
Regression test for #16311: the kernel checking of the `lia` proof below did not terminate in
practice, as it reduced `(2 ^ L - 1 - b) % 2 ^ 32 + (2 ^ 32 - 1)` with unary `Nat` arithmetic.
-/

theorem V3 (L b record ll A s1 z1 z2 : Nat)
  (f1 : 1 ≤ L)
  (f2 : L ≤ 7)
  (f9 : 2 * 2 ^ (L - 1) ≤ 2 ^ L)
  (f10 : 2 ^ L ≤ 2 * 2 ^ (L - 1))
  (f12 : b < 2 ^ (L - 1))
  (f16 : (2 ^ L - 1 - b) % 2 ^ 32 = 2 ^ L - 1 - b) :
  ((2 ^ L - 1 - b) % 2 ^ 32 + (2 ^ 32 - 1 % 2 ^ 32)) % 2 ^ 32 + 1 ≤ 2 ^ L := by
  lia

theorem t (x : Nat) : (x + 1 ≤ (x + 65535) % 65536 + 1) ↔ x ≤ (x + 65535) % 65536 := by
  simp only [Nat.reduceLeDiff]
