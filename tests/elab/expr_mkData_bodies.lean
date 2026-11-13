module

public import Lean.Expr
import all Lean.Expr
import all Lean.Level

/-!
`Expr.mkData`, `Expr.mkAppData` and `Level.mkData` run C (`src/kernel/expr.cpp`,
`src/kernel/level.cpp`) and have Lean bodies for the logic. This test compares the C-backed calls
with an independent transcription of the C on boundary and sample inputs, and proves from the bodies
the statements the kernel's cached-field cutoffs rely on.
-/

open Lean

/-! ## The C, transcribed on `UInt64` -/

/-- `lean_uint32_mix_hash` of `src/include/lean/lean.h`. -/
def cHash32 (h k : UInt32) : UInt32 :=
  let k := k * 0xcc9e2d51
  let k := k ^^^ (k >>> 15)
  let k := k * 0x1b873593
  let h := h ^^^ k
  let h := (h <<< 13) ||| (h >>> 19)
  h * 5 + 0xe6546b64

/-- `lean_expr_mk_data`, in range. -/
def cExprData (h : UInt32) (r : Nat) (d : UInt32) (a b c e : Bool) : UInt64 :=
  let d : UInt64 := if d > 255 then 255 else d.toUInt64
  let bit (x : Bool) (s : UInt64) : UInt64 := (if x then 1 else 0) <<< s
  h.toUInt64 + (d <<< 32) + bit a 40 + bit b 41 + bit c 42 + bit e 43 + (r.toUInt64 <<< 44)

/-- `lean_expr_mk_app_data`. -/
def cAppData (f a : UInt64) : UInt64 :=
  let depthOf (x : UInt64) : UInt64 := (x >>> 32) &&& (255 : UInt64)
  let depth := max (depthOf f) (depthOf a) + 1
  let depth := if depth > 255 then 255 else depth
  let range := max (f >>> 44) (a >>> 44)
  ((f ||| a) &&& ((15 : UInt64) <<< 40)) ||| (cHash32 f.toUInt32 a.toUInt32).toUInt64 ||| (depth <<< 32) |||
    (range <<< 44)

/-- `lean_level_mk_data`, in range. -/
def cLevelData (h : UInt64) (d : Nat) (m p : Bool) : UInt64 :=
  let bit (x : Bool) (s : UInt64) : UInt64 := (if x then 1 else 0) <<< s
  (h &&& (0xffffffff : UInt64)) + bit m 32 + bit p 33 + (d.toUInt64 <<< 40)

/-! ## Inputs -/

def bools : List Bool := [false, true]

def hashes : List UInt64 :=
  [0, 1, 0xffffffff, 0x100000000, 0xffffffffffffffff, 0xc6a4a7935bd1e995, 0x123456789abcdef0]

/-- Reproducible samples (a linear congruential generator). -/
def samples (n : Nat) : List UInt64 := Id.run do
  let mut x : UInt64 := 88172645463325252
  let mut r := []
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    r := x :: r
  return r

def exprDataWords : List UInt64 :=
  hashes ++ samples 200 ++
    ([Expr.mkData 0 1048575 255 true true true true, Expr.mkData 0 1048575 0, Expr.mkData 0 0 255,
      Expr.mkData 0xffffffff 1 254 true false true false] : List UInt64)

/-! ## The C-backed calls against the transcription -/

#guard hashes.all fun h => (hashes ++ samples 50).all fun k =>
  mixHash32 h.toUInt32 k.toUInt32 == cHash32 h.toUInt32 k.toUInt32

#guard (hashes.map UInt64.toUInt32).all fun h => [0, 1, 2, 1048574, 1048575].all fun r =>
  ([0, 1, 254, 255, 256, 0xffffffff] : List UInt32).all fun d =>
    bools.all fun a => bools.all fun b => bools.all fun c => bools.all fun e =>
      Expr.mkData h r d a b c e == cExprData h r d a b c e

#guard (samples 2000).all fun x =>
  let r := (x >>> 44).toNat
  let d := (x >>> 12).toUInt32
  let bit (s : UInt64) : Bool := (x >>> s) &&& (1 : UInt64) == (1 : UInt64)
  Expr.mkData x.toUInt32 r d (bit 0) (bit 1) (bit 2) (bit 3) ==
    cExprData x.toUInt32 r d (bit 0) (bit 1) (bit 2) (bit 3)

#guard exprDataWords.all fun f => exprDataWords.all fun a =>
  UInt64.toNat (Expr.mkAppData f a) == UInt64.toNat (cAppData f a)

#guard hashes.all fun h => [0, 1, 2, 16777214, 16777215].all fun d =>
  bools.all fun m => bools.all fun p =>
    UInt64.toNat (Level.mkData h d m p) == UInt64.toNat (cLevelData h d m p)

/-! ## From the bodies

The first two are the bodies' own statements; the proofs use no bound: above `1048575` and
`16777215` the C panics and the bodies compute the same formula. -/

example (h : UInt32) (r : Nat) (d : UInt32) (a b c e : Bool) :
    Expr.mkData h r d a b c e =
      UInt64.ofNat (h.toNat + (min 255 d.toNat) * 2 ^ 32 + a.toNat * 2 ^ 40 +
        b.toNat * 2 ^ 41 + c.toNat * 2 ^ 42 + e.toNat * 2 ^ 43 + r * 2 ^ 44) :=
  rfl

example (h : UInt64) (d : Nat) (m p : Bool) :
    Level.mkData h d m p =
      UInt64.ofNat (h.toUInt32.toNat + m.toNat * 2 ^ 32 + p.toNat * 2 ^ 33 + d * 2 ^ 40) :=
  rfl

/-! The third: an application's range is the maximum and its flags the disjunction. -/

theorem shiftRight_toNat (x k : UInt64) (hk : k.toNat < 64) :
    (x.shiftRight k).toNat = x.toNat / 2 ^ k.toNat := by
  show (x >>> k).toNat = _
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]

theorem flag_read (x k : UInt64) (hk : k.toNat < 64) :
    ((x.shiftRight k).land 1 == 1) = decide (x.toNat / 2 ^ k.toNat % 2 = 1) := by
  have h : ((x >>> k) &&& 1).toNat = x.toNat / 2 ^ k.toNat % 2 := by
    simp [UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.shiftRight_eq_div_pow,
      Nat.and_one_is_mod, Nat.mod_eq_of_lt hk]
  have hiff : (((x >>> k) &&& 1) = 1) ↔ x.toNat / 2 ^ k.toNat % 2 = 1 := by
    rw [← h, ← UInt64.toNat_inj]; rfl
  show (((x >>> k) &&& 1) == 1) = _
  rw [Bool.eq_iff_iff]; simp [hiff]

theorem range_read (x : Expr.Data) : x.looseBVarRange.toNat = UInt64.toNat x / 2 ^ 44 := by
  have hx : UInt64.toNat x < 2 ^ 64 := UInt64.toNat_lt x
  have h : (UInt64.shiftRight x 44).toNat = UInt64.toNat x / 2 ^ 44 :=
    shiftRight_toNat x 44 (by decide)
  show (UInt64.shiftRight x 44).toUInt32.toNat = _
  rw [UInt64.toNat_toUInt32, h]
  omega

theorem fvar_read (x : Expr.Data) : x.hasFVar = decide (UInt64.toNat x / 2 ^ 40 % 2 = 1) :=
  flag_read x 40 (by decide)

theorem emvar_read (x : Expr.Data) : x.hasExprMVar = decide (UInt64.toNat x / 2 ^ 41 % 2 = 1) :=
  flag_read x 41 (by decide)

theorem lmvar_read (x : Expr.Data) : x.hasLevelMVar = decide (UInt64.toNat x / 2 ^ 42 % 2 = 1) :=
  flag_read x 42 (by decide)

theorem lparam_read (x : Expr.Data) : x.hasLevelParam = decide (UInt64.toNat x / 2 ^ 43 % 2 = 1) :=
  flag_read x 43 (by decide)

section
variable (h : UInt32) (r : Nat) (d : UInt32) (a b c e : Bool) (hr : r ≤ 1048575)
include hr

theorem mkData_toNat :
    UInt64.toNat (Expr.mkData h r d a b c e) =
      h.toNat + (min 255 d.toNat) * 2 ^ 32 + a.toNat * 2 ^ 40 + b.toNat * 2 ^ 41 +
        c.toNat * 2 ^ 42 + e.toNat * 2 ^ 43 + r * 2 ^ 44 := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  show UInt64.toNat (UInt64.ofNat _) = _
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem mkData_range : (Expr.mkData h r d a b c e).looseBVarRange.toNat = r := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [range_read, mkData_toNat h r d a b c e hr]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem mkData_hasFVar : (Expr.mkData h r d a b c e).hasFVar = a := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [fvar_read, mkData_toNat h r d a b c e hr]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasExprMVar : (Expr.mkData h r d a b c e).hasExprMVar = b := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [emvar_read, mkData_toNat h r d a b c e hr]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasLevelMVar : (Expr.mkData h r d a b c e).hasLevelMVar = c := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [lmvar_read, mkData_toNat h r d a b c e hr]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasLevelParam : (Expr.mkData h r d a b c e).hasLevelParam = e := by
  have h1 : h.toNat < 2 ^ 32 := h.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [lparam_read, mkData_toNat h r d a b c e hr]
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

end

theorem range_le (x : Expr.Data) : x.looseBVarRange.toNat ≤ 1048575 := by
  have hx : UInt64.toNat x < 2 ^ 64 := UInt64.toNat_lt x
  rw [range_read]; omega

public theorem mkAppData_fields (f a : Expr.Data) :
    (Expr.mkAppData f a).looseBVarRange.toNat = max f.looseBVarRange.toNat a.looseBVarRange.toNat ∧
    (Expr.mkAppData f a).hasFVar = (f.hasFVar || a.hasFVar) ∧
    (Expr.mkAppData f a).hasExprMVar = (f.hasExprMVar || a.hasExprMVar) ∧
    (Expr.mkAppData f a).hasLevelMVar = (f.hasLevelMVar || a.hasLevelMVar) ∧
    (Expr.mkAppData f a).hasLevelParam = (f.hasLevelParam || a.hasLevelParam) := by
  have hr : max f.looseBVarRange.toNat a.looseBVarRange.toNat ≤ 1048575 :=
    Nat.max_le.2 ⟨range_le f, range_le a⟩
  exact ⟨mkData_range _ _ _ _ _ _ _ hr, mkData_hasFVar _ _ _ _ _ _ _ hr,
    mkData_hasExprMVar _ _ _ _ _ _ _ hr, mkData_hasLevelMVar _ _ _ _ _ _ _ hr,
    mkData_hasLevelParam _ _ _ _ _ _ _ hr⟩

/-- info: 'mkAppData_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mkAppData_fields
