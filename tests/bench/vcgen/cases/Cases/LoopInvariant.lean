import Lean
import Std.WP

/-!
One block of an unrolled loop in `StateM` over 64-bit registers, with one jump back to the loop
head and `n + 1` exits. Every exit re-establishes an invariant that relates `toNat` of the
registers to `len * 4` under the shared hypotheses `len % 4 = 0`, `len * 4 < 2 ^ 32` and
`rdx.setWidth 32 = BitVec.ofNat 32 len`. The loop has stride `2 ^ (n + 4)`.
Modeled on a loop invariant from an x86 verification of FFmpeg's `ff_scalarproduct_float_fma3`.
-/

open Lean Meta Order Std.WP

namespace LoopInvariant

structure M where
  rdi : BitVec 64
  rdx : BitVec 64
  rcx : BitVec 64
  r8 : BitVec 64
  lt : Bool

theorem M.rdi_mk {a b c d : BitVec 64} {e : Bool} : (M.mk a b c d e).rdi = a := rfl
theorem M.rdx_mk {a b c d : BitVec 64} {e : Bool} : (M.mk a b c d e).rdx = b := rfl
theorem M.rcx_mk {a b c d : BitVec 64} {e : Bool} : (M.mk a b c d e).rcx = c := rfl
theorem M.r8_mk {a b c d : BitVec 64} {e : Bool} : (M.mk a b c d e).r8 = d := rfl
theorem M.lt_mk {a b c d : BitVec 64} {e : Bool} : (M.mk a b c d e).lt = e := rfl

inductive Lbl where
  | loop
  | lvl (m : Nat)
  | done

def subR8 (k : Nat) : StateM M Unit := modify fun s => { s with r8 := s.r8 - BitVec.ofNat 64 k }
def cmpR8Rcx : StateM M Unit := modify fun s => { s with lt := s.r8.slt s.rcx }
def movRcxRdx : StateM M Unit := modify fun s => { s with rcx := s.rdx }
def andRcx (k : Nat) : StateM M Unit :=
  modify fun s => { s with rcx := s.rcx &&& BitVec.ofNat 64 k }
def cmpRcx (k : Nat) : StateM M Unit :=
  modify fun s => { s with lt := s.rcx.slt (BitVec.ofNat 64 k) }
def readLt : StateM M Bool := return (← get).lt

@[spec] theorem subR8_spec (k : Nat) (post : PUnit → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post ⟨⟩ { s with r8 := s.r8 - BitVec.ofNat 64 k } ⦄ subR8 k ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩
@[spec] theorem cmpR8Rcx_spec (post : PUnit → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post ⟨⟩ { s with lt := s.r8.slt s.rcx } ⦄ cmpR8Rcx ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩
@[spec] theorem movRcxRdx_spec (post : PUnit → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post ⟨⟩ { s with rcx := s.rdx } ⦄ movRcxRdx ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩
@[spec] theorem andRcx_spec (k : Nat) (post : PUnit → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post ⟨⟩ { s with rcx := s.rcx &&& BitVec.ofNat 64 k } ⦄ andRcx k ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩
@[spec] theorem cmpRcx_spec (k : Nat) (post : PUnit → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post ⟨⟩ { s with lt := s.rcx.slt (BitVec.ofNat 64 k) } ⦄ cmpRcx k ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩
@[spec] theorem readLt_spec (post : Bool → M → Prop) (eposts : EStack⟨⟩) :
    ⦃ fun s => post s.lt s ⦄ readLt ⦃ post; eposts ⦄ :=
  ⟨fun _ h => h⟩

theorem slt_eq_of_lt (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    a.slt b = decide (a.toNat < b.toNat) := by
  rw [BitVec.slt, BitVec.toInt_eq_toNat_of_lt (by omega), BitVec.toInt_eq_toNat_of_lt (by omega)]
  simp

theorem toNat_sub_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem toNat_and_ofNat_two_pow_sub_one {w : Nat} (x : BitVec w) (k : Nat) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.testBit_and, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · simp [hi]; exact Bool.and_comm _ _
  · simp [hi, BitVec.testBit_toNat, BitVec.getLsbD_of_ge x i (by omega)]

attribute [grind =] slt_eq_of_lt toNat_sub_le toNat_and_ofNat_two_pow_sub_one

def exits : Nat → StateM M Lbl
  | 0 => pure .done
  | j + 1 => cmpRcx (2 ^ (j + 4)) >>= fun _ => readLt >>= fun c =>
      if c then exits j else pure (.lvl (2 ^ (j + 4)))

def prog (n : Nat) : StateM M Lbl :=
  subR8 (2 ^ 64 - 2 ^ (n + 4)) >>= fun _ => cmpR8Rcx >>= fun _ => readLt >>= fun c =>
    if c then pure .loop
    else movRcxRdx >>= fun _ => andRcx (2 ^ (n + 4) - 1) >>= fun _ => exits n

def Goal (n : Nat) : Prop :=
  ∀ (len : Nat) (d : M), d.rdx.setWidth 32 = BitVec.ofNat 32 len → len % 4 = 0 → 0 < len →
    len * 4 < 2 ^ 32 → ∀ t : M,
    (t.rdi = d.rdi ∧ t.rdx.toNat = len * 4 ∧ t.rcx.toNat % 2 ^ (n + 4) = 0 ∧
      t.rcx.toNat ≤ len * 4 ∧ len * 4 < t.rcx.toNat + 2 ^ (n + 4) ∧
      t.r8.toNat % 2 ^ (n + 4) = 0 ∧ t.r8.toNat < t.rcx.toNat) →
    ⦃ fun s => s = t ⦄ prog n ⦃ fun l s => match l with
      | .loop => s.rdi = d.rdi ∧ s.rdx.toNat = len * 4 ∧ s.rcx.toNat % 2 ^ (n + 4) = 0 ∧
          s.rcx.toNat ≤ len * 4 ∧ len * 4 < s.rcx.toNat + 2 ^ (n + 4) ∧
          s.r8.toNat % 2 ^ (n + 4) = 0 ∧ s.r8.toNat < s.rcx.toNat ∧
          s.rcx.toNat - s.r8.toNat < t.rcx.toNat - t.r8.toNat
      | .lvl m => s.rdi = d.rdi ∧ s.rdx.toNat = len * 4 ∧ s.rcx.toNat + s.r8.toNat = len * 4 ∧
          m ≤ s.rcx.toNat ∧ s.rcx.toNat < 2 * m ∧ s.r8.toNat % (2 * m) = 0
      | .done => s.rdi = d.rdi ⦄

end LoopInvariant
