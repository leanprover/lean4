abbrev Var := Nat

structure Env (α : Type u) where
  ofNat : Nat → α
  add : α → α → α
  mul : α → α → α
  neg : α → α
  add_comm  : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero  : ∀ a, add a (ofNat 0) = a
  mul_comm  : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one   : ∀ a, mul a (ofNat 1) = a
  mul_zero  : ∀ a, mul a (ofNat 0) = ofNat 0
  left_dist : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  ofNat_add : ∀ k₁ k₂, ofNat (k₁ + k₂) = add (ofNat k₁) (ofNat k₂)
  ofNat_mul : ∀ k₁ k₂, ofNat (k₁ * k₂) = mul (ofNat k₁) (ofNat k₂)
  neg_add   : ∀ a b, neg (add a b) = add (neg a) (neg b)
  neg_mul   : ∀ a b, neg (mul a b) = mul (neg a) b
  neg_zero  : neg (ofNat 0) = ofNat 0
  neg_neg   : ∀ a, neg (neg a) = a

def Nat.env : Env Nat := {
  ofNat := id
  add   := Nat.add
  mul   := Nat.mul
  neg   := id
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  mul_comm := Nat.mul_comm
  mul_assoc := Nat.mul_assoc
  mul_one := Nat.mul_one
  mul_zero := Nat.mul_zero
  left_dist := Nat.left_distrib
  ofNat_add := fun _ _ => rfl
  ofNat_mul := fun _ _ => rfl
  neg_add := fun a b => rfl
  neg_mul := fun a b => rfl
  neg_neg := fun a => rfl
  neg_zero := rfl
}

theorem Env.zero_add (env : Env α) (a : α) : env.add (env.ofNat 0) a = a := by
  rw [add_comm, add_zero]

theorem Env.add_left_comm (env : Env α) (a b c : α) : env.add a (env.add b c) = env.add b (env.add a c) := by
  rw [← add_assoc, add_comm _ a b, add_assoc]

theorem Env.one_mul (env : Env α) (a : α) : env.mul (env.ofNat 1) a = a := by
  rw [mul_comm, mul_one]

theorem Env.zero_mul (env : Env α) (a : α) : env.mul (env.ofNat 0) a = env.ofNat 0 := by
  rw [mul_comm, mul_zero]

theorem Env.mul_left_comm (env : Env α) (a b c : α) : env.mul a (env.mul b c) = env.mul b (env.mul a c) := by
  rw [← mul_assoc, mul_comm _ a b, mul_assoc]

theorem Env.right_dist (env : Env α) (a b c : α) : env.mul (env.add a b) c = env.add (env.mul a c) (env.mul b c) := by
  rw [mul_comm, left_dist, mul_comm, mul_comm _ b c]

def hugeFuel := 100000000 -- any big number should work

structure Context (α : Type u) extends Env α where
  map : List α

def Var.denote (ctx : Context α) (v : Var) : α :=
  go ctx.map v (ctx.ofNat 0)
where
  go : List α → Nat → α → α
   | [],    i,   d  => d
   | a::as, 0,   d  => a
   | _::as, i+1, d  => go as i d

inductive Expr where
  | num (i : Nat)
  | var (v : Var)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (n : Expr)
  deriving Inhabited

def Expr.denote (ctx : Context α) : Expr → α
  | num n   => ctx.ofNat n
  | neg a   => ctx.neg (a.denote ctx)
  | var v   => v.denote ctx
  | add a b => ctx.add (a.denote ctx) (b.denote ctx)
  | mul a b => ctx.mul (a.denote ctx) (b.denote ctx)

abbrev Mon := List Var

def Mon.denote (ctx : Context α) : Mon → α
  | [] => ctx.ofNat 1
  | v::vs => ctx.mul (v.denote ctx) (denote ctx vs)

def Mon.mul (m₁ m₂ : Mon) : Mon :=
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : Mon :=
    match fuel with
    | 0 => m₁ ++ m₂
    | fuel + 1 =>
      match m₁, m₂ with
      | m₁, [] => m₁
      | [], m₂ => m₂
      | v₁ :: m₁, v₂ :: m₂ =>
        bif Nat.blt v₁ v₂ then
          v₁ :: go fuel m₁ (v₂ :: m₂)
        else bif Nat.blt v₂ v₁ then
          v₂ :: go fuel (v₁ :: m₁) m₂
        else
          v₁ :: v₂ :: go fuel m₁ m₂

abbrev Poly := List (Int × Mon)

def denoteInt (ctx : Context α) (i : Int) : α :=
  if i >= 0 then
    ctx.ofNat (Int.toNat i)
  else
    ctx.ofNat (Int.toNat (-i))

def Poly.denote (ctx : Context α) : Poly → α
  | [] => ctx.ofNat 0
  | (k, m) :: p => ctx.add (ctx.mul (denoteInt ctx k) (m.denote ctx)) (denote ctx p)

def Poly.add (p₁ p₂ : Poly) : Poly :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
    match fuel with
    | 0 => p₁ ++ p₂
    | fuel + 1 =>
      match p₁, p₂ with
      | p₁, [] => p₁
      | [], p₂ => p₂
      | (k₁, m₁) :: p₁, (k₂, m₂) :: p₂ =>
        bif m₁ < m₂ then
          (k₁, m₁) :: go fuel p₁ ((k₂, m₂) :: p₂)
        else bif m₂ < m₁ then
          (k₂, m₂) :: go fuel ((k₁, m₁) :: p₁) p₂
        else bif k₁ + k₂ == 0 then
          go fuel p₁ p₂
        else
          (k₁ + k₂, m₁) :: go fuel p₁ p₂

def Poly.mulMon (p : Poly) (k : Int) (m : Mon) : Poly :=
  match p with
  | [] => []
  | (k', m') :: p => (k*k', m.mul m') :: mulMon p k m

def Poly.mul (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ []
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | [] => acc
    | (k, m) :: p₁ => go p₁ (acc.add (p₂.mulMon k m))

def Poly.neg (p : Poly) : Poly :=
  match p with
  | [] => []
  | (k, m) :: p => (-k, m) :: neg p

def Expr.toPoly : Expr → Poly
  | Expr.num k   => bif k == 0 then [] else [(k, [])]
  | Expr.var v   => [(1, [v])]
  | Expr.add a b => a.toPoly.add b.toPoly
  | Expr.mul a b => a.toPoly.mul b.toPoly
  | Expr.neg a   => a.toPoly.neg

open Env

theorem denoteInt_one (ctx : Context α) : denoteInt ctx 1 = ctx.ofNat 1 := rfl

theorem denoteInt_zero (ctx : Context α) : denoteInt ctx 0 = ctx.ofNat 0 := rfl

theorem denoteInt_ofNat (ctx : Context α) : denoteInt ctx (Int.ofNat n) = ctx.ofNat n := by
  unfold denoteInt
  split
  next => rfl
  next h => sorry

theorem denoteInt_neg (ctx : Context α) (k : Int) : denoteInt ctx (-k) = ctx.neg (denoteInt ctx k) := by
  sorry
  -- match k with
  -- | .ofNat 0 => simp! [Neg.neg, neg_zero]
  -- | .ofNat (.succ n) => simp! [Neg.neg]
  -- | .negSucc n => simp! [Neg.neg, ofNat_add]; rw [← Nat.add_one]; simp! [ofNat_add, neg_neg]

theorem denoteInt_add (ctx : Context α) (k₁ k₂ : Int) : denoteInt ctx (k₁ + k₂) = ctx.add (denoteInt ctx k₁) (denoteInt ctx k₂) := by
  sorry
  -- cases k₁ <;> cases k₂ <;> simp! [HAdd.hAdd, Add.add, ofNat_add, neg_add, ← Nat.add_one, add_assoc, add_comm, add_left_comm]
  -- next n₁ n₂ => sorry
  -- next n₁ n₂ => sorry

theorem denoteInt_mul (ctx : Context α) (k₁ k₂ : Int) : denoteInt ctx (k₁ * k₂) = ctx.mul (denoteInt ctx k₁) (denoteInt ctx k₂) := by
  sorry
  -- cases k₁ <;> cases k₂ <;> simp! [HMul.hMul, Mul.mul, ofNat_mul]
  -- next n₁ n₂ => sorry
  -- next n₁ n₂ => sorry
  -- next n₁ n₂ => sorry

theorem Mon.append_denote (ctx : Context α) (m₁ m₂ : Mon) : (m₁ ++ m₂).denote ctx = ctx.mul (m₁.denote ctx) (m₂.denote ctx) := by
  match m₁ with
  | [] => simp! [one_mul]
  | v :: m₁ => simp! [append_denote ctx m₁ m₂, mul_assoc]

theorem Mon.mul_denote (ctx : Context α) (m₁ m₂ : Mon) : (m₁.mul m₂).denote ctx = ctx.mul (m₁.denote ctx) (m₂.denote ctx) :=
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : (Mon.mul.go fuel m₁ m₂).denote ctx = ctx.mul (m₁.denote ctx) (m₂.denote ctx) := by
    induction fuel generalizing m₁ m₂ with
    | zero => simp! [append_denote]
    | succ _ ih =>
      simp!
      split <;> simp!
      next => simp! [mul_one]
      next => simp! [one_mul]
      next v₁ m₁ v₂ m₂ =>
        by_cases hlt : Nat.blt v₁ v₂ <;> simp! [hlt, mul_assoc, ih]
        by_cases hgt : Nat.blt v₂ v₁ <;> simp! [hgt, mul_assoc, mul_comm, mul_left_comm, ih]

theorem Poly.neg_denote (ctx : Context α) (p : Poly) : p.neg.denote ctx = ctx.neg (p.denote ctx) := by
  match p with
  | [] => simp! [neg_zero]
  | (k, v) :: p => simp! [denoteInt_neg, neg_add, neg_mul, neg_denote ctx p]

theorem Poly.append_denote (ctx : Context α) (p₁ p₂ : Poly) : (p₁ ++ p₂).denote ctx = ctx.add (p₁.denote ctx) (p₂.denote ctx) := by
  match p₁ with
  | [] => simp! [zero_add]
  | v :: p₁ => simp! [append_denote _ p₁ p₂, add_assoc]

theorem Poly.add_denote (ctx : Context α) (p₁ p₂ : Poly) : (p₁.add p₂).denote ctx = ctx.add (p₁.denote ctx) (p₂.denote ctx) :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : (Poly.add.go fuel p₁ p₂).denote ctx = ctx.add (p₁.denote ctx) (p₂.denote ctx) := by
    induction fuel generalizing p₁ p₂ with
    | zero => simp! [append_denote]
    | succ _ ih =>
      simp!
      split <;> simp!
      next => simp! [add_zero]
      next => simp! [zero_add]
      next k₁ m₁ p₁ k₂ m₂ p₂ =>
        by_cases hlt : m₁ < m₂ <;> simp! [hlt, add_assoc, ih]
        by_cases hgt : m₂ < m₁ <;> simp! [hgt, add_assoc, add_comm, add_left_comm, ih]
        have : m₁ = m₂ := List.le_antisymm hgt hlt
        subst m₂
        by_cases heq : k₁ + k₂ == 0 <;> simp! [heq, ih]
        · rw [← add_assoc, ← right_dist, ← denoteInt_add, eq_of_beq heq, denoteInt_zero, zero_mul, zero_add]
        · simp [right_dist, left_dist, add_assoc, add_comm, add_left_comm, denoteInt_add]

theorem Poly.mulMon_denote (ctx : Context α) (p : Poly) (k : Int) (m : Mon) : (p.mulMon k m).denote ctx = ctx.mul (p.denote ctx) (ctx.mul (denoteInt ctx k) (m.denote ctx)) := by
  match p with
  | [] => simp! [zero_mul]
  | (k', m') :: p =>
    simp! [Mon.mul_denote, denoteInt_mul, right_dist, mulMon_denote ctx p, mul_assoc, mul_comm, mul_left_comm]

theorem Poly.mul_denote (ctx : Context α) (p₁ p₂ : Poly) : (p₁.mul p₂).denote ctx = ctx.mul (p₁.denote ctx) (p₂.denote ctx) := by
  simp [mul, go]; simp! [zero_add]
where
  go (p₁ : Poly) (acc : Poly) : (mul.go p₂ p₁ acc).denote ctx = ctx.add (acc.denote ctx) (ctx.mul (p₁.denote ctx) (p₂.denote ctx)) := by
    match p₁ with
    | [] => simp! [zero_mul, add_zero]
    | (k, m) :: p₁ =>
      simp! [go p₁, right_dist, add_denote, mulMon_denote,
             add_assoc, add_comm, add_left_comm,
             mul_assoc, mul_comm, mul_left_comm]

theorem Expr.toPoly_denote (ctx : Context α) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    · simp [eq_of_beq h]
    · simp [mul_one, add_zero, denoteInt_ofNat]
  | var v => simp! [mul_one, one_mul, add_zero, denoteInt_one]
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]
  | neg a => simp! [Poly.neg_denote, *]
