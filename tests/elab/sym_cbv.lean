/-! Tests for the `cbv` tactic in `grind`'s `sym =>` interactive mode. -/

example : Nat.succ 7 = 8 := by
  sym =>
    cbv

example (h : a = 8) : Nat.succ 7 = a := by
  sym =>
    cbv
    exact h.symm

example :
  have v :=
    BitVec.ofNat 64 ((BitVec.ofNat (64 - 0) ((BitVec.setWidth 64 (Int64.toBitVec 2)).toNat >>> 0)).toNat >>> 0) - 1;
  have v_1 := BitVec.ofNat 64 ((BitVec.ofNat (64 - 0) (v.toNat >>> 0)).toNat >>> 0) - 1;
  v ≠ v_1
:= by
  cbv
  intro hyp
  trivial

example :
  have v :=
    BitVec.ofNat 64 ((BitVec.ofNat (64 - 0) ((BitVec.setWidth 64 (Int64.toBitVec 2)).toNat >>> 0)).toNat >>> 0) - 1;
  have v_1 := BitVec.ofNat 64 ((BitVec.ofNat (64 - 0) (v.toNat >>> 0)).toNat >>> 0) - 1;
  v ≠ v_1
:= by
  sym =>
    cbv
    intro hyp
