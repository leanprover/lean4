import rc_model

/-!
Facts about `rc_model`'s counts, proved without `bv_decide`.

`rc_model.lean` proves most of its count lemmas with `bv_decide`, whose certificates are checked by
compiled code rather than by the kernel. The theorems of this directory use the few facts below
instead, so that their axioms stay within `propext`, `Classical.choice` and `Quot.sound`
(`Examples.lean` checks this). Each fact reduces a count to its signed value with `Int32.toInt` and
finishes with `omega`.
-/

namespace RcCounts

theorem toNat_toUInt32 (rc : Int32) :
    (rc.toUInt32.toNat : Int) = if rc.toInt < 0 then rc.toInt + 2 ^ 32 else rc.toInt := by
  have h1 : rc.toUInt32.toNat = rc.toBitVec.toNat := by
    rw [← UInt32.toNat_toBitVec, Int32.toBitVec_toUInt32]
  have h2 : rc.toInt = (rc.toBitVec.toNat : Int).bmod (2 ^ 32) := by
    rw [← Int32.toInt_toBitVec, BitVec.toInt_eq_toNat_bmod]
  have hlt : rc.toBitVec.toNat < 2 ^ 32 := rc.toBitVec.isLt
  rw [h1, h2]
  simp only [Int.bmod]
  have hm : ((rc.toBitVec.toNat : Int) % ((2 ^ 32 : Nat) : Int)) = rc.toBitVec.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  split <;> split <;> simp_all <;> omega

theorem stickyDrop_toInt : LEAN_RC_STICKY_DROP.toInt = -0x60000000 := by decide

/-- The unsigned guard of `lean_is_never_freed`, on the signed count. -/
theorem stickyDrop_unsigned (rc : Int32) :
    rc.toUInt32 ≤ LEAN_RC_STICKY_DROP.toUInt32 ↔ 0 ≤ rc.toInt ∨ rc.toInt ≤ -0x60000000 := by
  have hu : (LEAN_RC_STICKY_DROP.toUInt32.toNat : Int) = 0xA0000000 := by decide
  have hl := rc.toInt_lt; have hg := rc.le_toInt
  rw [UInt32.le_iff_toNat_le, ← Int.ofNat_le, hu, toNat_toUInt32]
  split <;> omega

theorem beq_toInt (rc c : Int32) : (rc == c) = (rc.toInt == c.toInt) := by
  rw [Bool.eq_iff_iff]; simp [Int32.toInt_inj]

theorem refCountNat_toInt (rc : Int32) :
    (refCountNat rc : Int) = if 0 < rc.toInt then rc.toInt else -rc.toInt := by
  have hl := rc.toInt_lt; have hu := rc.le_toInt
  simp only [refCountNat, refCount, isSt, Int64.toNatClampNeg, gt_iff_lt, decide_eq_true_eq]
  by_cases hp : (0 : Int32) < rc
  · have hp' : 0 < rc.toInt := by simpa [Int32.lt_iff_toInt_lt] using hp
    simp only [hp, ↓reduceIte, Int32.toInt_toInt64, hp']
    omega
  · have hp' : ¬ 0 < rc.toInt := by simpa [Int32.lt_iff_toInt_lt] using hp
    have hneg : (-rc.toInt64).toInt = -rc.toInt := by
      rw [Int64.toInt_neg, Int32.toInt_toInt64]
      apply Int.bmod_eq_of_le <;> omega
    simp only [hp, ↓reduceIte, hneg, hp']
    omega

theorem isNeverFreed_toInt (rc : Int32) :
    isNeverFreed rc = true ↔ (rc.toInt = 0 ∨ rc.toInt ≤ -0x60000000) := by
  simp only [isNeverFreed, isPersistent, isDropStopped, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, ← Int32.toInt_inj, Int32.toInt_zero, Int32.le_iff_toInt_le,
    stickyDrop_toInt]

theorem sub_one_toInt (rc : Int32) (h : 1 < rc.toInt) : (rc - 1).toInt = rc.toInt - 1 := by
  have := rc.toInt_lt
  rw [Int32.toInt_sub]; apply Int.bmod_eq_of_le <;> simp only [Int32.toInt_one] <;> omega

theorem add_one_toInt (rc : Int32) (h : rc.toInt < 0) : (rc + 1).toInt = rc.toInt + 1 := by
  have := rc.le_toInt
  rw [Int32.toInt_add]; apply Int.bmod_eq_of_le <;> simp only [Int32.toInt_one] <;> omega

/-- `decRef` in terms of the signed count. -/
theorem decRef_cases (rc : Int32) :
    decRef rc =
      if 1 < rc.toInt then some (rc - 1)
      else if rc.toInt = 1 then none
      else if rc.toInt = 0 ∨ rc.toInt ≤ -0x60000000 then some rc
      else if rc.toInt = -1 then none
      else some (rc + 1) := by
  have hm1 : (-1 : Int32).toInt = -1 := by decide
  have hl := rc.toInt_lt; have hu := rc.le_toInt
  rw [← decCascade_eq_decRef]
  simp only [decCascade, stickyDrop_unsigned rc, gt_iff_lt, Int32.lt_iff_toInt_lt, Int32.toInt_one,
    beq_toInt rc 1, beq_toInt rc (-1), hm1, beq_iff_eq]
  by_cases a : 1 < rc.toInt
  · simp [a]
  · by_cases b : rc.toInt = 1
    · simp [b]
    · by_cases c : rc.toInt = 0 ∨ rc.toInt ≤ -0x60000000
      · have c' : 0 ≤ rc.toInt ∨ rc.toInt ≤ -0x60000000 := by omega
        simp [a, b, c, c']
      · have c' : ¬ (0 ≤ rc.toInt ∨ rc.toInt ≤ -0x60000000) := by omega
        simp [a, b, c, c']

/-- `tracks_step` of `rc_model` for a drop, without `bv_decide`. -/
theorem tracks_dec (s : Option Int32) (t : Option Nat) (h : tracks s t) :
    tracks (s.bind decRef) (t.bind Op.dec.applyIdeal) := by
  match s, t with
  | none, none => rfl
  | none, some k => simp [tracks] at h
  | some rc, t =>
    have hl := rc.toInt_lt; have hu := rc.le_toInt
    simp only [Option.bind_some]
    rw [decRef_cases]
    by_cases nf : rc.toInt = 0 ∨ rc.toInt ≤ -0x60000000
    · have nf' := (isNeverFreed_toInt rc).mpr nf
      have h1 : ¬ 1 < rc.toInt := by omega
      have h2 : ¬ rc.toInt = 1 := by omega
      simp only [h1, h2, nf, ↓reduceIte]
      cases t with
      | none => simpa [tracks] using nf'
      | some k =>
        simp only [Option.bind_some, Op.applyIdeal]
        split <;> simp [tracks, nf']
    · have nf' : isNeverFreed rc = false := by
        cases hh : isNeverFreed rc
        · rfl
        · exact absurd ((isNeverFreed_toInt rc).mp hh) nf
      cases t with
      | none => simp [tracks, nf'] at h
      | some k =>
        simp only [tracks, nf', Bool.false_or, beq_iff_eq] at h
        have hk : (k : Int) = if 0 < rc.toInt then rc.toInt else -rc.toInt := by
          rw [← h, refCountNat_toInt]
        simp only [Option.bind_some, Op.applyIdeal, nf, ↓reduceIte]
        by_cases a : 1 < rc.toInt
        · have ha := sub_one_toInt rc a
          have hk' : (k : Int) = rc.toInt := by simpa [show 0 < rc.toInt by omega] using hk
          have hk1 : (k == 1) = false := by simp; omega
          have hr := refCountNat_toInt (rc - 1)
          rw [ha] at hr
          simp only [a, ↓reduceIte, hk1, Bool.false_eq_true, tracks, Bool.or_eq_true, beq_iff_eq]
          right
          simp only [show 0 < rc.toInt - 1 by omega, ↓reduceIte] at hr
          omega
        · by_cases b : rc.toInt = 1
          · have : k = 1 := by simp [b] at hk; omega
            simp [b, this, tracks]
          · by_cases d : rc.toInt = -1
            · have : k = 1 := by simp [d] at hk; omega
              simp [d, this, tracks]
            · have hb := add_one_toInt rc (by omega)
              have hk' : (k : Int) = -rc.toInt := by simpa [show ¬ 0 < rc.toInt by omega] using hk
              have hk1 : (k == 1) = false := by simp; omega
              have hr := refCountNat_toInt (rc + 1)
              rw [hb] at hr
              simp only [a, b, d, ↓reduceIte, hk1, Bool.false_eq_true, tracks, Bool.or_eq_true,
                beq_iff_eq]
              right
              simp only [show ¬ 0 < rc.toInt + 1 by omega, ↓reduceIte] at hr
              omega

/-- A drop leaves a never-freed count alone. -/
theorem decRef_neverFreed (rc : Int32) (h : isNeverFreed rc = true) : decRef rc = some rc := by
  have c := (isNeverFreed_toInt rc).mp h
  rw [decRef_cases]
  have h1 : ¬ 1 < rc.toInt := by omega
  have h2 : ¬ rc.toInt = 1 := by omega
  simp [h1, h2, c]

/-- No drop brings a count into the never-freed range. -/
theorem decRef_not_neverFreed (rc rc' : Int32) (h : isNeverFreed rc = false)
    (hd : decRef rc = some rc') : isNeverFreed rc' = false := by
  have hl := rc.toInt_lt; have hu := rc.le_toInt
  have hn : ¬ (rc.toInt = 0 ∨ rc.toInt ≤ -0x60000000) := fun c => by
    have := (isNeverFreed_toInt rc).mpr c; simp_all
  rw [decRef_cases] at hd
  cases h' : isNeverFreed rc' with
  | false => rfl
  | true =>
    have c' := (isNeverFreed_toInt rc').mp h'
    by_cases a : 1 < rc.toInt
    · simp only [a, ↓reduceIte, Option.some.injEq] at hd
      subst hd
      have ha := sub_one_toInt rc a
      omega
    · by_cases b : rc.toInt = 1
      · simp [b] at hd
      · simp only [a, b, hn, ↓reduceIte] at hd
        by_cases d : rc.toInt = -1
        · simp [d] at hd
        · simp only [d, ↓reduceIte, Option.some.injEq] at hd
          subst hd
          have hb := add_one_toInt rc (by omega)
          omega

end RcCounts
