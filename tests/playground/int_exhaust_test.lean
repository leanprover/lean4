import Lean.Util.TestNormalForms
import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Meta.LitValues

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

namespace Nat

attribute [simp] mod_one
attribute [simp] Nat.mul_div_cancel
attribute [simp] Nat.mul_div_cancel_left

theorem succ_mod (a b : Nat) : (a + 1) % b = if a % b + 1 = b then 0 else (a % b) + 1 := by
  match b with
  | 0 =>
    simp
  | 1 =>
    simp
  | b + 2 =>
    simp only [Nat.succ.injEq]
    split <;> rename_i dp
    · rw [Nat.add_mod a 1 _]
      simp [dp]
    · have one_lt : 1 < b + 2 := Nat.le_add_left ..
      have q : a % (b + 2) ≤ b + 1 := Nat.le_of_succ_le_succ (Nat.mod_lt _ (by omega))
      have a_lt : a % (b + 2) + 1 < b + 2 := Nat.succ_lt_succ (Nat.lt_of_le_of_ne q dp)
      rw [Nat.add_mod a 1 _, Nat.mod_eq_of_lt one_lt, Nat.mod_eq_of_lt a_lt]

theorem le_div_iff_mul_le' (hb : 0 < b) : a ≤ c / b ↔ a * b ≤ c := le_div_iff_mul_le hb

protected theorem div_le_div_right {a b : Nat} (h : a ≤ b) (c : Nat) : a / c ≤ b / c :=
  (c.eq_zero_or_pos.elim fun hc => by simp [hc]) fun hc ↦
    (le_div_iff_mul_le' hc).2 <| Nat.le_trans (Nat.div_mul_le_self _ _) h

theorem sub_div_dvd (a : Nat) {b c : Nat} (h : c ∣ b) : (a - b) / c = a / c - b / c := by
  let ⟨d, p⟩ := h
  match c with
  | 0 =>
    simp
  | c + 1 =>
    have sd := Nat.sub_mul_div a (c+1) d
    if le : (c + 1) * d ≤ a then
      simp [p, sd le, Nat.mul_comm c d, Nat.mul_div_cancel]
    else
      have q := Nat.le_of_not_le le
      have r := Nat.div_le_of_le_mul q
      simp [p, Nat.sub_eq_zero_of_le, q, r]

@[simp] theorem sub_div_self (a b : Nat) : (a - b) / b = a / b - 1 := by
  match b with
  | 0 => simp
  | b + 1 => simp [sub_div_dvd, Nat.zero_lt_succ, Nat.div_self]

theorem div_eq_to_mul (a b c : Nat) (h : b > 0) : a / b = c ↔ a = b * c + a % b := by
  apply Iff.intro
  · intro p
    simp [←p]
    exact (div_add_mod a b).symm
  · intro p
    conv at p => lhs; rw [← div_add_mod a b]
    replace p := Nat.add_right_cancel p
    replace p := Nat.mul_left_cancel h p
    exact p

theorem eq_sub_iff (a : Nat) {b c : Nat} (p : b ≥ c) : (a = b - c) ↔ (a + c = b) := by
  rw [@Eq.comm _ a, Nat.sub_eq_iff_eq_add p, @Eq.comm _ b]

theorem mul_div_self (a b : Nat) : b * (a / b) = a - a % b := by
  conv => rhs; lhs; rw [← Nat.div_add_mod a b]
  simp

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

attribute [simp] Int.dvd_neg
attribute [simp] Int.dvd_refl
attribute [simp] Int.dvd_natAbs

@[simp]theorem dvd_mod_self (a b : Int) : (a ∣ b % a) ↔ a ∣ b := by
  have p : a ∣ -(a * (b / a)) := by
    simp [Int.dvd_neg, Int.dvd_mul_right]
  simp [Int.emod_def, Int.sub_eq_add_neg, Int.dvd_add_left p]

attribute [simp] emod_self

theorem add_ofNat_ofNat (m n : Nat) : (m : Int) + (n : Int) = (m + n : Nat) := rfl
theorem add_ofNat_negSucc (m n : Nat) : m + -[n+1] = subNatNat m (n + 1) := rfl
theorem add_negSucc_ofNat (m n : Nat) : -[m+1] + n = subNatNat n (m + 1) := rfl
theorem add_negSucc_negSucc (m n : Nat) : -[m+1] + -[n+1] = -[m + n + 1 +1] := rfl

theorem ediv_ofNat_ofNat (m n : Nat) : (m : Int) / (n : Int) = (m / n : Nat) := rfl

--set_option trace.Meta.Tactic.simp.rewrite true

/-
@[simp] theorem add_ediv_right (a : Int) {b : Int} (h : b ≠ 0) : (a + b) / b = (a / b) + 1 := by
  match a, b with
  | .ofNat a, .ofNat b => admit
  | .ofNat a, -[b +1] => admit
  | _, 0 => simp at h
  | -[a+1], .ofNat (b + 1) =>
    simp [-Int.natCast_add, add_negSucc_ofNat, subNatNat, ediv_negSucc_succ,
          Int.neg_add_cancel_right]
    split;
    · simp only [Int.ediv_ofNat_ofNat]
      --natCast_add] -- [ediv_ofNat_ofNat];
      admit
    · admit
  | -[a+1], -[b+1] => simp [ediv_negSucc_negSucc]; admit
-/

/-
  | ofNat m, ofNat n => ofNat (m / n)
  | ofNat m, -[n+1]  => -ofNat (m / succ n)
  | -[_+1],  0       => 0
  | -[m+1],  ofNat (succ n) => -[m / succ n +1]
  | -[m+1],  -[n+1]  => ofNat (succ (m / succ n))
-/



/-
@[simp] theorem add_ediv_left (a : Int) {b : Int} (h : b ≠ 0) : (b + a) / b = (a / b) + 1 := by
  rw [Int.add_comm, add_ediv_right a h]
-/

theorem emod_neg_iff (m n : Int) : m % n < 0 ↔ (m < 0 ∧ n = 0) := by
  change Int.emod m n < 0 ↔ (m < 0 ∧ n = 0)
  match m with
  | ofNat m =>
    have not_lt_zero (n : Nat) : ¬((n : Int) < 0) := by
      apply (Int.ofNat_not_neg _).mp
      -- (Int.ofNat_zero_le _)
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

@[simp] theorem sub_emod_self_left (n y : Int) : (n - y) % n = (-y) % n := by
  simp [Int.sub_eq_add_neg]

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
    simp [Int.div, ediv_negSucc_succ, Nat.succ_div,
          Int.negSucc_lt_zero, q, true_and,
          -Int.natCast_add]
    split <;> rename_i pg
    · simp [Int.neg_add]
    · simp [Int.neg_add, Int.neg_add_cancel_right]
  | -[m +1], -[n +1] => by
    simp [Int.div, ediv_negSucc_negSucc,
      Int.negSucc_lt_zero,
      -ofNat_ediv, -natCast_add,
      Nat.succ_div]
    split <;> rename_i h
    . simp
    · simp [Int.add_neg_cancel_right]

theorem mod_eq_emod' (a b : Int) : Int.mod a b = a % b - b * ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0 := by
  simp [emod_def, mod_def, div_eq_ediv',
        Int.mul_add, Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]


@[simp] theorem emod_mod (a b : Int) : (mod a b) % b = a % b := by
  simp [Int.mod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg]

@[simp] theorem mod_emod (m n : Int) : Int.mod (m % n) n = m % n := by
  simp_all [mod_eq_emod', emod_neg_iff]

@[simp] theorem mod_mod (m n : Int) : Int.mod (Int.mod m n) n = Int.mod m n := by
  simp only [mod_eq_emod' m n]
  split
  · rename_i mnn
    rw [mod_eq_emod']
    by_cases q : OfNat.ofNat 0 < natAbs n <;>
    simp_all [Int.sub_eq_add_neg, Int.mul_sign, add_emod_of_dvd, Int.add_lt_iff,
              Int.natAbs_pos, Int.emod_lt, Int.dvd_add_left]
  · simp [mod_emod]

@[simp] theorem emod_fmod (a b : Int) : (fmod a b) % b = a % b := by
  simp [Int.fmod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg]

@[simp] theorem fmod_emod (m n : Int) : Int.fmod (m % n) n = Int.fmod m n := by
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
deriving DecidableEq, Hashable, Inhabited, Repr

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
  deriving DecidableEq, Repr

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

def mkLit (i : Int) (tp : NumType) : NumTerm :=
  if i < 0 then
    match tp with
    | .nat => panic! "Negative number passed into nat"
    | .int => neg (lit ((- i).toNat) .int)
  else
    lit i.toNat tp

def asIntLit (i : NumTerm) : Option Int :=
  match i with
  | .lit n _ => some (n : Int)
  | .neg (.lit n .int) => some (- (n : Int))
  | _ => none


/-

  1 + i0 - i0 reduces to
  1
but is expected to reduce to
  1 + i0 - i0


  i0 - i1 + i1 reduces to
  i0
but is expected to reduce to
  i0 - i1 + i1
  -/
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
    | _, _ => Id.run <| do
      if let .sub xa xb _ := x then
        if tp = .int ∧ xb == y then
          return xa
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return (mkLit (i+j) tp)
      pure v
  | sub x y tp =>
    match x, y, tp with
    | x, lit 0 _, _ => x
    | lit 0 _, _, .nat => lit 0 .nat
    | lit 0 _, y, .int => simp (neg y)
    | x, y, _ => Id.run <| do
      match tp with
      | .nat =>
        if let (lit i _, lit j _) := (x, y) then
          return lit (i-j) .nat
      | .int =>
        if let (some i, some j) := (asIntLit x, asIntLit y) then
          return mkLit (i - j) .int
      if let .add xa xb _ := x then
        if xb == y then
          return xa
      if x == y then
        return .lit 0 tp
      pure v
  | neg x =>
    match x with
    | lit n _ => intLit (- (Int.ofNat n))
    | neg x => x
    | _ => v
  | mul x y tp =>
    match x, y with
    | _, lit 0 _ => y
    | lit 0 _, _ => x
    | _, lit 1 _ => x
    | lit 1 _, _ => y
    | lit i _, lit j _ => lit (i*j) tp
    | _, _ => Id.run <| do
      if let (some i, some j) := (asIntLit x, asIntLit y) then
        return (mkLit (i * j) tp)
      pure v
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
      lit 0 op.typeOf
    else if let lit 1 _ := y then
      x
    else Id.run <| do
      if let add xa xb _tp := x then
        if let .lit i _ := y then
          if op ∈ [.divNat] ∧ i ≠ 0 then
            if xa == y then
              return simp (.add (.div xb y op) (.lit 1 op.typeOf) op.typeOf)
            else if xb == y then
              return simp (.add (.div xa y op) (.lit 1 op.typeOf) op.typeOf)
      if let sub xa xb _tp := x then
          if op = .divNat ∧ xb == y then
            return simp (.sub (.div xa y op) (.lit 1 op.typeOf) op.typeOf)
      if let mod _ n mOp := x then
        if op = .divNat ∧ mOp = .divNat ∧ n == y then
          return .lit 0 .nat
      if let neg xn := x then
        match op with
        | .tdivInt =>
          return simp (neg (div xn y op))
        | _ =>
          pure ()
      if let neg yn := y then
        match op with
        | .edivInt | .tdivInt =>
          return simp (neg (div x yn op))
        | _ =>
          pure ()
      if let mul xa xb _ := x then
       if let .lit i _ := y then
          if i ≠ 0 then
            if xa == y then
              return xb
            if xb == y then
              return xa
      pure v
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
      if let add xa xb _tp := x then
        if op ∈ [.divNat, .edivInt] then
          if xa == n then
            return simp (.mod xb n op)
          else if xb == n then
            return simp (.mod xa n op)
          if let mul xba xbb _tp := xb then
            if xba == n || xbb == n then
              return simp (.mod xa n op)
      if let sub xa xb _tp := x then
        if op ∈ [.edivInt] then
          if xa == n then
            return simp (.mod (.neg xb) n op)
          else if xb == n then
            return simp (.mod xa n op)
          if let mul xba xbb _tp := xb then
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
            | .fdivInt, .edivInt => some .fdivInt
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
    panic! s!"simp result changed types:\n  Input: {repr u}\n  Out:   {repr v}"

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
--set_option pp.coercions false
--set_option pp.notation false
--set_option pp.explicit true
#intTest

section
variable (i0 : Int)

set_option trace.Meta.Tactic.simp true


end
namespace Nat

end Nat

namespace Int

open Lean.Meta.CheckTactic (CheckGoalType)

example (b : Int) : div (2 * b) 2 = b := by
  simp
  --admit

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
