import Lean.Util.TestNormalForms
import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Meta.LitValues

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

namespace Nat

attribute [simp] mod_one


theorem succ_mod (a b : Nat) : (a + 1) % b = if a % b + 1 = b then 0 else (a % b) + 1 := by
  match b with
  | 0 =>
    simp
  | 1 =>
    simp
  | b + 2 =>
    simp only [Nat.succ.injEq]
    split
    · rename_i dp
      rw [Nat.add_mod a 1 _]
      simp [dp]
    · rename_i dp
      have one_lt : 1 < b + 2 := Nat.le_add_left ..
      have q : a % (b + 2) ≤ b + 1 := Nat.le_of_succ_le_succ (Nat.mod_lt _ (by omega))
      have a_lt : a % (b + 2) + 1 < b + 2 := Nat.succ_lt_succ (Nat.lt_of_le_of_ne q dp)
      rw [Nat.add_mod a 1 _]
      rw [Nat.mod_eq_of_lt one_lt, Nat.mod_eq_of_lt a_lt]

theorem sub_div {x n : Nat} (h : n ≤ x) : (x - n) / n = x / n - 1 := by
  have sd := Nat.sub_mul_div x n 1
  simp [Nat.mul_one] at sd
  exact sd h

theorem eq_sub_iff (a : Nat) {b c : Nat} (p : b ≥ c) : (a = b - c) ↔ (a + c = b) := by
  rw [@Eq.comm _ a, Nat.sub_eq_iff_eq_add p, @Eq.comm _ b]

theorem mul_div_self (a b : Nat) : b * (a / b) = a - a % b := by
  conv => rhs; lhs; rw [← Nat.div_add_mod a b]
  simp

theorem dvd_sub_iff {a b : Nat} (h : a ≥ b) : b ∣ (a - b) ↔ b ∣ a := by
  apply Iff.intro
  · intro ⟨c, p⟩
    replace p := Nat.eq_add_of_sub_eq h p
    apply Exists.intro (c+1)
    simp [Nat.mul_add, p]
  · intro ⟨c, p⟩
    match c with
    | 0 =>
      simp_all
    | c + 1 =>
      apply Exists.intro c
      simp [p, Nat.mul_add]

theorem succ_mod_d (a b : Nat) : (a + 1) % b = if b ∣ (a+1) then 0 else a % b + 1 := by
  match b with
  | 0 => simp
  | b + 1 =>
    match Nat.lt_trichotomy (a+1) (b+1) with
    | Or.inl q =>
      have p : a < b + 1 := Nat.le_succ_of_le (Nat.le_of_succ_le_succ q)
      split
      · rename_i dvd
        replace dvd := Nat.mod_eq_zero_of_dvd dvd
        simp only [Nat.mod_eq_of_lt q] at dvd
      · rename_i dvd
        simp only [Nat.mod_eq_of_lt, p, q]
    | Or.inr (Or.inl p) =>
      simp [←p]
    | Or.inr (Or.inr p) =>
      replace p : a ≥ b + 1 := Nat.le_of_succ_le_succ p
      have q : a + 1 ≥ b + 1 := Nat.le_succ_of_le p
      have r := succ_mod_d (a - (b + 1)) (b + 1)
      simp only [←Nat.sub_add_comm p, ←Nat.mod_eq_sub_mod p, ←Nat.mod_eq_sub_mod q,
        Nat.dvd_sub_iff q] at r
      exact r

theorem succ_div_d (a b : Nat) : (a + 1) / b = if b ∣ (a+1) then a / b + 1 else a / b := by
  match b with
  | 0 =>
    simp
  | b + 1 =>
    match Nat.lt_trichotomy (a+1) (b+1) with
    | Or.inl q =>
      have p : a < b + 1 := Nat.le_succ_of_le (Nat.le_of_succ_le_succ q)
      split
      · rename_i dvd
        replace dvd := Nat.mod_eq_zero_of_dvd dvd
        simp only [Nat.mod_eq_of_lt q] at dvd
      · rename_i dvd
        simp only [Nat.div_eq_of_lt, p, q]
    | Or.inr (Or.inl p) =>
      simp [←p, Nat.div_self, Nat.div_eq_of_lt]
    | Or.inr (Or.inr p) =>
      replace p : a ≥ b + 1 := Nat.le_of_succ_le_succ p
      have q : a + 1 ≥ b + 1 := Nat.le_succ_of_le p
      have r := succ_div_d (a - (b + 1)) (b + 1)
      simp only [←Nat.sub_add_comm p, Nat.dvd_sub_iff q] at r
      have b_pos : 0 < b + 1 := Nat.succ_le_succ (Nat.zero_le b)
      rw [Nat.div_eq_sub_div b_pos p, Nat.div_eq_sub_div b_pos q, r]
      split <;> simp

end Nat

namespace Int

section
open Lean.Meta Simp

def reduceBinIntNatOp (name : Name) (op : Int → Nat → Int) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity name 2 do return .continue
  let some v₁ ← getIntValue? e.appFn!.appArg! | return .continue
  let some v₂ ← getNatValue? e.appArg! | return .continue
  return .done <| toExpr (op v₁ v₂)

dsimproc [simp, seval] reduceTDiv (Int.div _ _) := reduceBin ``Int.div 2 Int.div
dsimproc [simp, seval] reduceTMod (Int.mod _ _) := reduceBin ``Int.mod 2 Int.mod
dsimproc [simp, seval] reduceFDiv (Int.fdiv _ _) := reduceBin ``Int.fdiv 2 Int.fdiv
dsimproc [simp, seval] reduceFMod (Int.fmod _ _) := reduceBin ``Int.fmod 2 Int.fmod
dsimproc [simp, seval] reduceBdiv (bdiv _ _) := reduceBinIntNatOp ``bdiv bdiv
dsimproc [simp, seval] reduceBmod (bmod _ _) := reduceBinIntNatOp ``bmod bmod

end

protected theorem sub_lt_iff (a b c : Int) : a - b < c ↔ a < b + c :=
  Iff.intro Int.lt_add_of_sub_left_lt Int.sub_left_lt_of_lt_add

protected theorem add_lt_iff (a b c : Int) : a + b < c ↔ a < -b + c := by
  apply Iff.intro
  · intro p
    apply @Int.lt_of_add_lt_add_left b
    simp [Int.add_comm b a, Int.add_neg_cancel_left, p]
  · intro p
    apply @Int.lt_of_add_lt_add_left (-b)
    simp [Int.add_comm (-b) (a + b), Int.add_neg_cancel_right, Int.add_comm c (-b), p]

theorem ofNat_not_neg (a : Nat) : (a : Int) < 0 ↔ False := by
  simp only [iff_false]
  apply Int.not_le_of_gt
  simp [Int.add_le_add_iff_left]

theorem ediv_ofNat_negSucc (m n : Nat) : m / -[n+1] = -ofNat (m / Nat.succ n) := rfl
theorem ediv_negSucc_zero (m : Nat) : -[m+1] / 0 = 0 := rfl
theorem ediv_negSucc_succ (m n : Nat) : -[m+1] / (n + 1 : Nat) = -((m / (n + 1)) : Nat) + (-1) := by
  simp [HDiv.hDiv, Div.div, Int.ediv, Int.negSucc_coe', Int.sub_eq_add_neg]
theorem ediv_negSucc_negSucc (m n : Nat) : -[m+1] / -[n+1] = ((m / (n + 1) + 1) : Nat) := rfl

theorem emod_ofNat   (a : Nat) (b : Int) : Nat.cast a % b = Nat.cast (a % b.natAbs) := rfl
theorem emod_negSucc (a : Nat) (b : Int) : -[a+1] % b = (b.natAbs : Int) - (a % b.natAbs + 1) := rfl


@[simp]
theorem dvd_natCast_natCast (a b : Nat) : (a : Int) ∣ (b : Int) ↔ a ∣ b := by
  simp [Int.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, mod, Int.emod_ofNat,
    -emod_ofNat]
  apply Int.ofNat_inj

@[simp]
theorem dvd_natCast_negSucc (a b : Nat) : (a : Int) ∣ -[ b +1] ↔ a ∣ b+1 := by
  simp [Int.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, mod, Int.emod_ofNat,
    -emod_ofNat]
  apply Int.ofNat_inj

set_option trace.Meta.Tactic.simp.rewrite true

@[simp]
theorem dvd_negSucc (a : Nat) (b : Int) : -[a +1] ∣ b ↔ (((a+1 : Nat) : Int) ∣ b) := by
  apply Iff.intro
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]

theorem dvd_negSucc_negSucc (a b : Nat) : -[a +1] ∣ -[ b +1] ↔ a+1 ∣ b+1 := by
  simp [-natCast_add, dvd_natCast_negSucc]

attribute [simp] Int.dvd_neg
attribute [simp] Int.dvd_refl
attribute [simp] Int.dvd_natAbs

--theorem dvd_sub_self (a b : Int) : (a ∣ b - a) ↔ a ∣ b := by
--  simp [Int.sub_eq_add_neg, Int.dvd_add_left]

theorem dvd_sub_natAbs (a b : Int) : (a ∣ (b - a.natAbs)) ↔ a ∣ b := by
  simp [Int.sub_eq_add_neg, Int.dvd_add_left]

@[simp]
theorem dvd_mod_self (a b : Int) : (a ∣ (b % a)) ↔ a ∣ b := by
  have p : a ∣ -(a * (b / a)) := by
    simp [Int.dvd_neg, Int.dvd_mul_right]
  simp [Int.emod_def, Int.sub_eq_add_neg, Int.dvd_add_left p]

attribute [simp] emod_self

theorem emod_neg_iff (m n : Int) : m % n < 0 ↔ (m < 0 ∧ n = 0) := by
  change Int.emod m n < 0 ↔ (m < 0 ∧ n = 0)
  match m with
  | ofNat m =>
    have not_lt_zero (n : Nat) : ¬((n : Int) < 0) := by
      intro p
      apply Nat.not_lt_zero _ (Int.ofNat_lt.mp p)
    simp [-ofNat_emod, Int.emod, not_lt_zero]
  | -[m+1] =>
    simp [-ofNat_emod, -Int.natCast_add, Int.emod, Int.subNatNat_eq_coe, negSucc_lt_zero,
          Int.sub_lt_iff]
    apply Iff.intro
    · intro p
      replace p := Nat.le_of_succ_le_succ p
      if nz : n = 0 then
        exact nz
      else
        have q : n.natAbs > 0 := Int.natAbs_pos.mpr nz
        have r : m % n.natAbs < n.natAbs := Nat.mod_lt _ q
        exact False.elim (Nat.not_le_of_gt r p)
    · intro p
      simp [p]

theorem add_emod_of_dvd (a b c : Int) (p : c ∣ b) : (a + b) % c = a % c := by
  let ⟨d, eq⟩ := p
  simp [eq]

theorem emod_sub_natAbs_self (m n : Int) : (m - n.natAbs) % n = m % n := by
  simp [Int.sub_eq_add_neg, add_emod_of_dvd]

theorem emod_lt (a b : Int) (h : b ≠ 0) : a % b < Int.natAbs b := by
  rw [emod_as_nat_mod]
  if p : a ≥ 0 then
    simp [p, -Int.ofNat_emod]
    exact Nat.mod_lt _ (by omega)
  else
    simp [p, -Int.ofNat_emod]
    apply Int.sub_lt_self
    apply Int.succ_ofNat_pos

theorem div_eq_ediv' (a b : Int) : Int.div a b = a / b + ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0  :=
  match a, b with
  | (a : Nat), ofNat b => rfl
  | (a : Nat), -[b +1] => by
    simp [Int.div, ediv_ofNat_negSucc, ofNat_not_neg]
  | -[a +1], 0 => by
    simp [Int.div, ediv_negSucc_zero]
  | -[a +1], (b+1 : Nat) => by
    have q : ¬(Nat.cast ((b + 1) : Nat) = (0 : Int)) := by
      norm_cast
    simp [-Int.natCast_add] at q
    simp [Int.div, ediv_negSucc_succ, Nat.succ_div_d,
          Int.negSucc_lt_zero, q, true_and,  dvd_natCast_negSucc,
          -Int.natCast_add]
    split <;> rename_i pg
    · simp [Int.neg_add]
    · simp [Int.neg_add, Int.neg_add_cancel_right]
  | -[m +1], -[n +1] => by
    simp [Int.div, ediv_negSucc_negSucc,
      dvd_natCast_negSucc,
      Int.negSucc_lt_zero,
      -ofNat_ediv, -natCast_add,
      Nat.succ_div_d]
    split <;> rename_i h
    . simp
    · simp [Int.add_neg_cancel_right]

theorem mod_eq_emod' (a b : Int) : Int.mod a b = a % b - b * ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0 := by
  simp [emod_def, mod_def, div_eq_ediv',
        Int.mul_add, Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]

@[simp]
theorem mod_emod (m n : Int) : Int.mod (m % n) n = m % n := by
  simp_all [mod_eq_emod', emod_neg_iff]

@[simp]
theorem mod_mod (m n : Int) : Int.mod (Int.mod m n) n = Int.mod m n := by
  simp only [mod_eq_emod' m n]
  split
  · rename_i mnn
    rw [mod_eq_emod']
    by_cases q : OfNat.ofNat 0 < natAbs n <;>
    simp_all [Int.sub_eq_add_neg, Int.mul_sign, add_emod_of_dvd, Int.add_lt_iff,
              Int.natAbs_pos, Int.emod_lt, Int.dvd_add_left]
  · simp [mod_emod]

#print fmod_eq_emod

--theorem div_eq_ediv' (a b : Int) : Int.div a b = + ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0  :=

#print Int.fdiv

/-
  match a, b with
  | (a : Nat), ofNat b => rfl
  | (a : Nat), -[b +1] => by
    simp [Int.div, ediv_ofNat_negSucc, ofNat_not_neg]
  | -[a +1], 0 => by
    simp [Int.div, ediv_negSucc_zero]
  | -[a +1], (b+1 : Nat) => by
    have q : ¬(Nat.cast ((b + 1) : Nat) = (0 : Int)) := by
      norm_cast
    simp [-Int.natCast_add] at q
    simp [Int.div, ediv_negSucc_succ, Nat.succ_div_d,
          Int.negSucc_lt_zero, q, true_and,  dvd_natCast_negSucc,
          -Int.natCast_add]
    split <;> rename_i pg
    · simp [Int.neg_add]
    · simp [Int.neg_add, Int.neg_add_cancel_right]
  | -[m +1], -[n +1] => by
    simp [Int.div, ediv_negSucc_negSucc,
      dvd_negSucc_negSucc,
      Int.negSucc_lt_zero,
      -ofNat_ediv, -natCast_add,
      Nat.succ_div_d]
    split <;> rename_i h
    . simp
    · simp [Int.add_neg_cancel_right]
-/


theorem fdiv_eq_ediv' (a b : Int) : Int.fdiv a b = a / b + if b < 0 ∧ ¬(b ∣ a) then (-1) else 0 := by
  match a, b with
  | 0,       b       =>
    simp [Int.fdiv, Int.dvd_zero]
  | ofNat (Nat.succ m), ofNat n =>
    simp [Int.fdiv, Int.ofNat_not_neg]
  | ofNat (Nat.succ m), -[n+1] =>
    simp [-Int.natCast_add, -Int.ofNat_ediv, Int.fdiv, ediv_ofNat_negSucc, Nat.succ_div_d]
    split
    · rename_i h
      simp [-Int.natCast_add, h, Int.negSucc_lt_zero]
      rfl
    · rename_i h
      have p : (m : Int) + 1 ≠ 0 := by omega
      simp [-Int.natCast_add, -Int.ofNat_ediv, h, Int.negSucc_lt_zero]
      simp [Int.negSucc_eq, Int.neg_add, p]
  | -[_+1],  0       =>
    simp
  | -[m+1],  ofNat (Nat.succ n) => rfl
  | -[m+1],  -[n+1]  =>
    simp [-Int.natCast_add, -Int.ofNat_ediv, Int.fdiv, Int.ediv_negSucc_negSucc, Nat.succ_div_d]
    split
    · rename_i h
      simp [-Int.natCast_add, -Int.ofNat_ediv, ediv_ofNat_negSucc, Int.negSucc_lt_zero, h]
    · rename_i h
      simp [-Int.natCast_add, -Int.ofNat_ediv, Int.negSucc_lt_zero, h]
      simp [Int.natCast_add, Int.add_neg_cancel_right]

theorem fmod_eq_emod' (a b : Int) : Int.fmod a b = a % b - b * ite (b < 0 ∧ ¬(b ∣ a)) (-1) 0 := by
  simp [fmod_def, emod_def, fdiv_eq_ediv', Int.sub_eq_add_neg, Int.mul_add, Int.neg_add,
        Int.add_assoc]

@[simp]
theorem fmod_emod (m n : Int) : Int.fmod (m % n) n = Int.fmod m n := by
  simp_all [fmod_eq_emod', emod_neg_iff]

@[simp]
theorem fmod_fmod (m n : Int) : Int.fmod (Int.fmod m n) n = Int.fmod m n := by
  simp [fmod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg,
        Int.dvd_add_left, Int.dvd_mul_right]

--@[simp] theorem zero_bdiv : bdiv 0 n = 0 := by sorry

--@[simp] theorem bdiv_one : bdiv m 1 = 0 := by sorry

@[simp] theorem zero_bdiv (n : Nat) : bdiv 0 n = 0 := by
  unfold bdiv; simp; omega
@[simp] theorem bdiv_zero  (n : Int) : bdiv n 0 = 0 := by rfl

@[simp] theorem bdiv_one   (n : Int) : bdiv n 1 = n := by unfold bdiv; simp

@[simp] theorem bmod_zero (n : Int) : bmod n 0 = n := by unfold bmod; simp

end Int

inductive NumType where
| nat
| int
deriving BEq, Hashable, Inhabited, Repr

protected def NumType.render [Monad M] [MonadQuotation M] (v : NumType) : M Term := do
  match v with
  | nat => `(Nat)
  | int => `(Int)

inductive  DivMode where
  | divNat
  | edivInt
  | tdivInt
  | fdivInt
  | bdivInt
  deriving BEq, Repr

def DivMode.typeOf (m : DivMode) : NumType :=
  match m with
  | divNat => .nat
  | edivInt => .int
  | fdivInt => .int
  | tdivInt => .int
  | bdivInt => .int

inductive NumTerm where
  | var (d : VarDecl NumType)
  | lit (n : Nat) (tp : NumType)
  | natToInt (x : NumTerm)
  | intToNat (x : NumTerm)
  | add (x y : NumTerm) (tp : NumType)
  | sub (x y : NumTerm) (tp : NumType)
  | neg (x : NumTerm)
  | mul (x y : NumTerm) (tp : NumType)
  | div (x y : NumTerm) (m : DivMode)
  | mod (x y : NumTerm) (m : DivMode)
  deriving BEq, Inhabited, Repr

namespace NumTerm

open NumType

partial def map (f : NumTerm → NumTerm) (v : NumTerm) : NumTerm :=
  match v with
  | var _ | lit _ _ => v
  | natToInt x => natToInt (f x)
  | intToNat x => intToNat (f x)
  | add x y tp => add (f x) (f y) tp
  | sub x y tp => sub (f x) (f y) tp
  | neg x => neg (f x)
  | mul x y tp => mul (f x) (f y) tp
  | div x y op => div (f x) (f y) op
  | mod x y op => mod (f x) (f y) op

protected def typeOf (v : NumTerm) : NumType :=
  match v with
  | var d => d.type
  | lit _ tp => tp
  | natToInt _ => .int
  | intToNat _ => .nat
  | add _ _ tp => tp
  | sub _ _ tp => tp
  | neg _ => .int
  | mul _ _ tp => tp
  | div _ _ op => op.typeOf
  | mod _ _ op => op.typeOf

protected def render [Monad M] [MonadQuotation M] (v : NumTerm) : M Term := do
  match v with
  | var d => pure d.ident
  | lit n tp => `(($(Syntax.mkNumLit (toString n)) : $(←tp.render)))
  | natToInt x => `((($(←x.render) : Nat) : Int))
  | intToNat x => `((($(←x.render) : Int) : Nat))
  | add x y tp => `((($(←x.render) + $(←y.render)) : $(←tp.render)))
  | sub x y _ => `($(←x.render) - $(←y.render))
  | neg x => `(- $(←x.render))
  | mul x y _ => `($(←x.render) * $(←y.render))
  | div x y op =>
    match op with
    | .divNat  => `($(←x.render) / $(←y.render))
    | .edivInt => `($(←x.render) / $(←y.render))
    | .fdivInt => `(Int.fdiv $(←x.render) $(←y.render))
    | .tdivInt => `(Int.div  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bdiv $(←x.render) $(←y.render))
  | mod x y op =>
    match op with
    | .divNat  => `($(←x.render) % $(←y.render))
    | .edivInt => `($(←x.render) % $(←y.render))
    | .fdivInt => `(Int.fmod $(←x.render) $(←y.render))
    | .tdivInt => `(Int.mod  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bmod $(←x.render) $(←y.render))

instance : GenTerm NumTerm NumType where
  render := NumTerm.render
  mkVar := NumTerm.var

def intLit (i : Int) : NumTerm :=
  if i < 0 then
    neg (lit ((- i).toNat) .int)
  else
    lit i.toNat .int

def asIntLit (i : NumTerm) : Option Int :=
  match i with
  | .lit n _ => some (n : Int)
  | .neg (.lit n .int) => some (- (n : Int))
  | _ => none

partial def simp (v : NumTerm) : NumTerm :=
  let v := map simp v
  match v with
  | natToInt x =>
    (match x with
    | lit n _ => lit n .int
    | add x y _ => add (natToInt x) (natToInt y) .int
    | mul x y _ => mul (natToInt x) (natToInt y) .int
    | div x y _ => div (natToInt x) (natToInt y) .edivInt
    | mod x y _ => mod (natToInt x) (natToInt y) .edivInt
    | var _ | sub _ _ _ | neg _ | intToNat _ | natToInt _ => v)
  | add x y tp =>
    match x, y with
    | x, lit 0 _ => x
    | lit 0 _, y => y
    | lit i _, lit j _ => lit (i+j) tp
    | _, _ => v
  | sub x y tp =>
    match x, y, tp with
    | x, lit 0 _, _ => x
    | lit i _, lit j _, .nat => lit (i-j) tp
    | lit i _, lit j _, .int => intLit ((i : Int) - (j : Int))
    | lit 0 _, _, .nat => lit 0 .nat
    | lit 0 _, y, .int => simp (neg y)
    | x, y, _ =>
      if x == y then
        .lit 0 tp
      else
        v
  | neg x =>
    match x with
    | lit n _ => intLit (- (Int.ofNat n))
    | _ => v
  | mul x y tp =>
    match x, y with
    | _, lit 0 _ => y
    | lit 0 _, _ => x
    | _, lit 1 _ => x
    | lit 1 _, _ => y
    | lit i _, lit j _ => lit (i*j) tp
    | _, _ => v
  | div x y op =>
    if let (some x, some y) := (asIntLit x, asIntLit y) then
      match op with
      | .divNat => lit (Nat.div x.toNat y.toNat) .nat
      | .edivInt => intLit (Int.ediv x y)
      | .fdivInt => intLit (Int.fdiv x y)
      | .tdivInt => intLit (Int.div  x y)
      | .bdivInt => intLit (Int.bdiv x y.toNat)
    else if let lit 0 _ := x then
      x
    else if let lit 0 _ := y then
      y
    else if let lit 1 _ := y then
      x
    else
      v
  | mod x n op =>
    if let (some x, some n) := (asIntLit x, asIntLit n) then
      match op with
      | .divNat => lit (Nat.mod x.toNat n.toNat) .nat
      | .edivInt => intLit (Int.emod x n)
      | .fdivInt => intLit (Int.fmod x n)
      | .tdivInt => intLit (Int.mod  x n)
      | .bdivInt => intLit (Int.bmod x n.toNat)
    else if let lit 0 _ := x then
      x
    else if let lit 0 _ := n then
      x
    else if let lit 1 _ := n then
      lit 0 op.typeOf
    else if x == n then
      lit 0 op.typeOf
    else Id.run do
      if let add xa xb tp := x then
        if let .edivInt := op then
          if xa == n then
            return simp (.mod xb n op)
          else if xb == n then
            return simp (.mod xa n op)
          if let mul xba xbb tp := xb then
            if xba == n || xbb == n then
              return simp (.mod xa n op)
      if let mul xa xb tp := x then
        if xa == n || xb == n then
          return lit 0 tp
      if let mod xn xd xop := x then
        if xd == n then
          let rop :=
            match op, xop with
            | .divNat, .divNat => some .divNat
            | .edivInt, _ => some .edivInt
            | .tdivInt, .edivInt => some .edivInt
            | .tdivInt, .tdivInt => some .tdivInt
            | .fdivInt, .edivInt => some .edivInt
            | .fdivInt, .fdivInt => some .fdivInt
            | .bdivInt, _ => some .bdivInt
            | _, _ => none
          if let some rop := rop then
            return simp (mod xn n rop)
      if let neg yn := n then
        match op with
        | .edivInt | .tdivInt | .bdivInt =>
          return simp (mod x yn op)
        | _ =>
          pure ()
      return v
  | _ => v

partial def simpv (u : NumTerm) : NumTerm :=
  let v := simp u
  if v.typeOf == u.typeOf then
    v
  else
    panic! s!"{repr u} has changed types."

def litOp (n : Nat) (tp : NumType) := mkOp [] tp fun _ => lit n tp
def addOp (tp : NumType) := mkOp [tp, tp] tp fun a => add (a[0]!) (a[1]!) tp
def subOp (tp : NumType) := mkOp [tp, tp] tp fun a => sub (a[0]!) (a[1]!) tp
def negOp : Op NumType NumTerm := mkOp [.int] .int fun a => neg (a[0]!)
def mulOp (tp : NumType) := mkOp [tp, tp] tp fun a => mul (a[0]!) (a[1]!) tp
def divOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => div (a[0]!) (a[1]!) op
def modOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => mod (a[0]!) (a[1]!) op

end NumTerm

open NumTerm

syntax:lead (name := intTestElab) "#intTest" : command

@[command_elab intTestElab]
def elabIntTest : CommandElab := fun _stx => do
  let types : List NumType := [.nat, .int]
  let ops := [
      litOp 0 .nat,
      litOp 1 .nat,
      litOp 2 .nat,
      litOp 0 .int,
      litOp 1 .int,
      litOp 2 .int,
      addOp .nat, addOp .int,
      subOp .nat, subOp .int,
      negOp,
      mulOp .nat, mulOp .int,
      divOp .divNat, divOp .edivInt, divOp .fdivInt, divOp .tdivInt, divOp .bdivInt .nat,
      modOp .divNat, modOp .edivInt, modOp .fdivInt, modOp .tdivInt, modOp .bdivInt .nat,
  ]
  let vars : List (NumType × CoreM Command) := [
      (.nat, `(variable (n : Nat))),
      (.int, `(variable (i : Int)))
  ]
  let stats : GenStats := { maxTermSize := 6, maxDepth := 3, maxVarCount := 2 }
  testNormalForms types ops vars NumTerm.simpv stats

set_option maxHeartbeats 100000000
set_option pp.coercions false
--set_option pp.explicit true
#intTest


namespace Int

--set_option pp.explicit true


set_option trace.Meta.Tactic.simp.rewrite true

example (i : Int) : (2 + i) % i = 2 % i := by
  simp

theorem div_as_nat (x y : Int) : Int.div x y =
  ite (x ≥ 0) 1 (-1) * ite (y ≥ 0) 1 (-1) * ((x.natAbs) / (y.natAbs)) := by
  cases x <;> cases y <;>  simp [Int.div, ofNat_nonneg, ←Int.neg_eq_neg_one_mul]

/-
def emod : (@& Int) → (@& Int) → Int
  | ofNat m, n => ofNat (m % natAbs n)
  | -[m+1],  n => subNatNat (natAbs n) (succ (m % natAbs n))
-/

set_option trace.Meta.Tactic.simp.rewrite true


--@[simp] theorem add_mod_self {a b : Int} : Int.mod(a + b)  b = a % b := by
--  have := add_mul_emod_self_left a b 1; rwa [Int.mul_one] at this

theorem negSucc_in_add (a b : Nat) : -[a + b +1] = -[a+1] - b := by
  cases b <;> rfl

end Int
