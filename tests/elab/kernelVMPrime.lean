/-!
A verified `Lean.KernelVM` program: trial division. `noDiv_sound` proves that a successful run of
`noDivProg` on `p` shows that `p` has no divisor `d` with `2 ≤ d` and `d * d ≤ p`, and `prime_ex`
uses it by kernel evaluation, without `Lean.ofReduceBool`.
-/

open Lean.KernelVM

/-- Trial division of input 0 by `2, 3, …` while `i ≤ p / i`. -/
def noDivProg : Prog where
  body :=
    .seq (.set 0 (.const 2))
    (.while (.bin .ule (.reg 0) (.bin .udiv (.input 0 (.const 0)) (.reg 0)))
      (.seq (.assert (.bin .eq (.bin .eq (.bin .umod (.input 0 (.const 0)) (.reg 0)) (.const 0)) (.const 0)))
        (.set 0 (.bin .add (.reg 0) (.const 1)))))


/-- The invariant of the trial division loop. -/
def NoDivInv (p : Nat) (st : State) : Prop :=
  2 ≤ (readD st.regs 0).toNat ∧ ∀ d, 2 ≤ d → d < (readD st.regs 0).toNat → p % d ≠ 0

theorem noDiv_sound (p fuel : Nat) (hp : p < 2 ^ 64) (h : run noDivProg [p] fuel = true) :
    ∀ d, 2 ≤ d → d * d ≤ p → p % d ≠ 0 := by
  have hpn : (UInt64.ofNat p).toNat = p := by simp [Nat.mod_eq_of_lt hp]
  have e0 : (UInt64.ofNat 0).toNat = 0 := rfl
  have g0 : p.getUInt64 0 = p := by simp [Nat.getUInt64, Nat.mod_eq_of_lt hp]
  have gi : getInput [p] 0 = p := rfl
  have z : UInt64.ofNat 0 = 0 := rfl
  have t : Triple [p] (fun st => st = {}) noDivProg.body (fun _ => ∀ d, 2 ≤ d → d * d ≤ p → p % d ≠ 0) := by
    refine Triple.seq (R := NoDivInv p) (Triple.conseq Triple.set ?_) (Triple.while (NoDivInv p) ?_ ?_)
    · rintro st rfl v hv
      simp [Exp.eval] at hv; subst hv
      simp [NoDivInv, readD_writeD]
      intro d h1 h2; omega
    · refine Triple.seq (R := fun st => NoDivInv p st ∧ (readD st.regs 0).toNat ≤ p / (readD st.regs 0).toNat ∧ p % (readD st.regs 0).toNat ≠ 0)
        (Triple.conseq Triple.assert ?_) (Triple.conseq Triple.set ?_)
      · rintro st ⟨hI, v, hv, hv0⟩ w hw hw0
        simp only [Exp.eval, BinOp.eval, Option.some.injEq] at hv hw
        subst hv hw
        simp only [z, gi, UInt64.toNat_zero, g0, ofBool_ne_zero, decide_eq_true_eq,
          beq_iff_eq, ofBool_eq_zero, beq_eq_false_iff_ne, UInt64.toNat_ofNat', UInt64.ofNat_toNat] at hv0 hw0
        simp only [UInt64.le_iff_toNat_le, UInt64.toNat_div, hpn, Nat.shiftRight_zero, Nat.mul_zero] at hv0
        simp only [ne_eq, ← UInt64.toNat_inj, UInt64.toNat_mod, hpn, Nat.shiftRight_zero, Nat.mul_zero] at hw0
        exact ⟨hI, hv0, hw0⟩
      · rintro st ⟨⟨h2, hI⟩, hle, hmod⟩ v hv
        simp only [Exp.eval, BinOp.eval, Option.some.injEq] at hv
        subst hv
        have hlt : (readD st.regs 0).toNat + 1 < 2 ^ 64 := by
          have := Nat.div_le_self p (readD st.regs 0).toNat
          have := Nat.div_le_div_left (a := p) h2 (by omega)
          omega
        have h1 : (UInt64.ofNat 1).toNat = 1 := rfl
        simp only [NoDivInv, readD_writeD, ite_true, UInt64.toNat_add, h1]
        rw [Nat.mod_eq_of_lt hlt]
        refine ⟨by omega, fun d hd hdi => ?_⟩
        by_cases hdeq : d = (readD st.regs 0).toNat
        · subst hdeq; exact hmod
        · exact hI d hd (by omega)
    · rintro st ⟨h2, hI⟩ hc
      simp only [Exp.eval, BinOp.eval, Option.some.injEq] at hc
      intro d hd hdd hmod
      simp only [gi, e0, g0, ofBool_eq_zero, decide_eq_false_iff_not, UInt64.le_iff_toNat_le,
        UInt64.toNat_div, hpn, Nat.not_le] at hc
      by_cases hdi : d < (readD st.regs 0).toNat
      · exact hI d hd hdi hmod
      · have : p < (readD st.regs 0).toNat * (readD st.regs 0).toNat := by
          have := (Nat.div_lt_iff_lt_mul (by omega)).1 hc; exact this
        have : (readD st.regs 0).toNat * (readD st.regs 0).toNat ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
        omega
  obtain ⟨_, hQ⟩ := Triple.run t h
  exact hQ

/-- A use: `1000000000039` has no divisor `d` with `2 ≤ d` and `d * d ≤ 1000000000039`. -/
theorem prime_ex : ∀ d, 2 ≤ d → d * d ≤ 1000000000039 → 1000000000039 % d ≠ 0 :=
  noDiv_sound 1000000000039 10000000 (by decide) (by decide +kernel)

/--
info: 'prime_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prime_ex
