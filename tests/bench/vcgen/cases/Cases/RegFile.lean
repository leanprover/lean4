import Lean
import Std.WP

/-!
A register file in `StateM`. Each `step` adds `1` to every register, through the `Regs.get` and
`Regs.set` accessors. The `@[vcgen_simp]` theorems turn `s.set .rK v` into a structure literal and
`(Regs.mk …).rK` into a field, so `vcgen` keeps the state as one `Regs.mk` literal as it produces
the state.
-/

open Lean Meta Order Std.WP

namespace RegFile

set_option experimental.vcgen true

inductive R where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7
  deriving DecidableEq

structure Regs where
  r0 : BitVec 64
  r1 : BitVec 64
  r2 : BitVec 64
  r3 : BitVec 64
  r4 : BitVec 64
  r5 : BitVec 64
  r6 : BitVec 64
  r7 : BitVec 64

def Regs.get (s : Regs) : R → BitVec 64
  | .r0 => s.r0
  | .r1 => s.r1
  | .r2 => s.r2
  | .r3 => s.r3
  | .r4 => s.r4
  | .r5 => s.r5
  | .r6 => s.r6
  | .r7 => s.r7

def Regs.set (s : Regs) (r : R) (v : BitVec 64) : Regs :=
  match r with
  | .r0 => { s with r0 := v }
  | .r1 => { s with r1 := v }
  | .r2 => { s with r2 := v }
  | .r3 => { s with r3 := v }
  | .r4 => { s with r4 := v }
  | .r5 => { s with r5 := v }
  | .r6 => { s with r6 := v }
  | .r7 => { s with r7 := v }

@[vcgen_simp] theorem Regs.set_r0 (s : Regs) (v : BitVec 64) : s.set .r0 v = { s with r0 := v } := rfl
@[vcgen_simp] theorem Regs.set_r1 (s : Regs) (v : BitVec 64) : s.set .r1 v = { s with r1 := v } := rfl
@[vcgen_simp] theorem Regs.set_r2 (s : Regs) (v : BitVec 64) : s.set .r2 v = { s with r2 := v } := rfl
@[vcgen_simp] theorem Regs.set_r3 (s : Regs) (v : BitVec 64) : s.set .r3 v = { s with r3 := v } := rfl
@[vcgen_simp] theorem Regs.set_r4 (s : Regs) (v : BitVec 64) : s.set .r4 v = { s with r4 := v } := rfl
@[vcgen_simp] theorem Regs.set_r5 (s : Regs) (v : BitVec 64) : s.set .r5 v = { s with r5 := v } := rfl
@[vcgen_simp] theorem Regs.set_r6 (s : Regs) (v : BitVec 64) : s.set .r6 v = { s with r6 := v } := rfl
@[vcgen_simp] theorem Regs.set_r7 (s : Regs) (v : BitVec 64) : s.set .r7 v = { s with r7 := v } := rfl
@[vcgen_simp] theorem Regs.get_r0 (s : Regs) : s.get .r0 = s.r0 := rfl
@[vcgen_simp] theorem Regs.get_r1 (s : Regs) : s.get .r1 = s.r1 := rfl
@[vcgen_simp] theorem Regs.get_r2 (s : Regs) : s.get .r2 = s.r2 := rfl
@[vcgen_simp] theorem Regs.get_r3 (s : Regs) : s.get .r3 = s.r3 := rfl
@[vcgen_simp] theorem Regs.get_r4 (s : Regs) : s.get .r4 = s.r4 := rfl
@[vcgen_simp] theorem Regs.get_r5 (s : Regs) : s.get .r5 = s.r5 := rfl
@[vcgen_simp] theorem Regs.get_r6 (s : Regs) : s.get .r6 = s.r6 := rfl
@[vcgen_simp] theorem Regs.get_r7 (s : Regs) : s.get .r7 = s.r7 := rfl
@[vcgen_simp] theorem Regs.r0_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r0 = a0 := rfl
@[vcgen_simp] theorem Regs.r1_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r1 = a1 := rfl
@[vcgen_simp] theorem Regs.r2_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r2 = a2 := rfl
@[vcgen_simp] theorem Regs.r3_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r3 = a3 := rfl
@[vcgen_simp] theorem Regs.r4_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r4 = a4 := rfl
@[vcgen_simp] theorem Regs.r5_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r5 = a5 := rfl
@[vcgen_simp] theorem Regs.r6_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r6 = a6 := rfl
@[vcgen_simp] theorem Regs.r7_mk {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64} : (Regs.mk a0 a1 a2 a3 a4 a5 a6 a7).r7 = a7 := rfl

attribute [vcgen_simp] BitVec.add_assoc

def addi (d a : R) (i : BitVec 64) : StateM Regs Unit := modify fun s => s.set d (s.get a + i)

@[spec] theorem addi_spec (d a : R) (i : BitVec 64) (post : PUnit → Regs → Prop) :
    ⦃fun s => post ⟨⟩ (s.set d (s.get a + i))⦄ addi d a i ⦃post⦄ :=
  ⟨fun _ h => h⟩

def step : StateM Regs Unit := do
  addi .r0 .r0 1
  addi .r1 .r1 1
  addi .r2 .r2 1
  addi .r3 .r3 1
  addi .r4 .r4 1
  addi .r5 .r5 1
  addi .r6 .r6 1
  addi .r7 .r7 1

def loop (n : Nat) : StateM Regs Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop :=
  ∀ s₀, ⦃fun s => s = s₀⦄ loop n ⦃fun _ s =>
    s.get .r0 = s₀.get .r0 + BitVec.ofNat 64 n ∧ s.get .r1 = s₀.get .r1 + BitVec.ofNat 64 n ∧ s.get .r2 = s₀.get .r2 + BitVec.ofNat 64 n ∧ s.get .r3 = s₀.get .r3 + BitVec.ofNat 64 n ∧ s.get .r4 = s₀.get .r4 + BitVec.ofNat 64 n ∧ s.get .r5 = s₀.get .r5 + BitVec.ofNat 64 n ∧ s.get .r6 = s₀.get .r6 + BitVec.ofNat 64 n ∧ s.get .r7 = s₀.get .r7 + BitVec.ofNat 64 n⦄

end RegFile
