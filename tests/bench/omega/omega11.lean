theorem t
(a b : BitVec 64)
(an bn : Nat)
(han : an > 0)
(hbn : bn > 0)
(ha : a.toNat + an ≤ 18446744073709551616)
(hb : b.toNat + bn ≤ 18446744073709551616)
(hsep : a.toNat + an ≤ b.toNat ∨ a.toNat ≥ b.toNat + bn) :
((¬b - a ≤ a + BitVec.ofNat 64 an - 1#64 - a ∧ ¬b + BitVec.ofNat 64 bn - 1#64 - a ≤ a + BitVec.ofNat 64 an - 1#64 - a) ∧ ¬a - b ≤ b + BitVec.ofNat 64 bn - 1#64 - b) ∧ ¬a + BitVec.ofNat 64 an - 1#64 - b ≤ b + BitVec.ofNat 64 bn - 1#64 - b := by
  bv_omega
