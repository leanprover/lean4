abbrev Var := Nat

structure Env (α : Type u) where
  ofInt : Int → α
  add : α → α → α
  mul : α → α → α
  sub : α → α → α
  add_comm  : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero  : ∀ a, add a (ofInt 0) = a
  mul_comm  : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one   : ∀ a, mul a (ofInt 1) = a
  mul_zero  : ∀ a, mul a (ofInt 0) = ofInt 0
  sub_def   : ∀ a b, sub a b = add a (mul (ofInt (-1)) b)
  left_dist : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  ofInt_add : ∀ k₁ k₂, ofInt (k₁ + k₂) = add (ofInt k₁) (ofInt k₂)
  ofInt_mul : ∀ k₁ k₂, ofInt (k₁ * k₂) = mul (ofInt k₁) (ofInt k₂)

theorem Env.zero_add (env : Env α) (a : α) : env.add (env.ofInt 0) a = a := by
  rw [add_comm, add_zero]

theorem Env.add_left_comm (env : Env α) (a b c : α) : env.add a (env.add b c) = env.add b (env.add a c) := by
  rw [← add_assoc, add_comm _ a b, add_assoc]

theorem Env.one_mul (env : Env α) (a : α) : env.mul (env.ofInt 1) a = a := by
  rw [mul_comm, mul_one]

theorem Env.zero_mul (env : Env α) (a : α) : env.mul (env.ofInt 0) a = env.ofInt 0 := by
  rw [mul_comm, mul_zero]

theorem Env.mul_left_comm (env : Env α) (a b c : α) : env.mul a (env.mul b c) = env.mul b (env.mul a c) := by
  rw [← mul_assoc, mul_comm _ a b, mul_assoc]

theorem Env.right_dist (env : Env α) (a b c : α) : env.mul (env.add a b) c = env.add (env.mul a c) (env.mul b c) := by
  rw [mul_comm, left_dist, mul_comm, mul_comm _ b c]

def hugeFuel := 100000000 -- any big number should work

structure Context (α : Type u) extends Env α where
  map : List α

def Var.denote (ctx : Context α) (v : Var) : α :=
  go ctx.map v (ctx.ofInt 0)
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
  | sub (a b : Expr)
  deriving Inhabited

def Expr.denote (ctx : Context α) : Expr → α
  | num n   => ctx.ofInt n
  | var v   => v.denote ctx
  | add a b => ctx.add (a.denote ctx) (b.denote ctx)
  | mul a b => ctx.mul (a.denote ctx) (b.denote ctx)
  | sub a b => ctx.sub (a.denote ctx) (b.denote ctx)

abbrev Mon := List Var

def Mon.denote (ctx : Context α) : Mon → α
  | [] => ctx.ofInt 1
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

def Poly.denote (ctx : Context α) : Poly → α
  | [] => ctx.ofInt 0
  | (k, m) :: p => ctx.add (ctx.mul (ctx.ofInt k) (m.denote ctx)) (denote ctx p)

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

def Poly.insertSorted (k : Int) (m : Mon) (p : Poly) : Poly :=
  match p with
  | [] => [(k, m)]
  | (k', m') :: p => bif m < m' then (k, m) :: (k', m') :: p else (k', m') :: insertSorted k m p

def Poly.mulMon (p : Poly) (k : Int) (m : Mon) : Poly :=
  go p []
where
  go (p : Poly) (acc : Poly) : Poly :=
    match p with
    | [] => acc
    | (k', m') :: p => go p (acc.insertSorted (k*k') (m.mul m'))

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
  | (k, v) :: p => ((-1)*k, v) :: neg p

def Expr.toPoly : Expr → Poly
  | num k   => bif k == 0 then [] else [(k, [])]
  | var v   => [(1, [v])]
  | add a b => a.toPoly.add b.toPoly
  | mul a b => a.toPoly.mul b.toPoly
  | sub a b => a.toPoly.add b.toPoly.neg
open Env

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
        · rw [← add_assoc, ← right_dist, ← ofInt_add, eq_of_beq heq, zero_mul, zero_add]
        · simp [right_dist, left_dist, add_assoc, add_comm, add_left_comm, ofInt_add]

theorem Poly.denote_insertSorted (ctx : Context α) (k : Int) (m : Mon) (p : Poly) : (p.insertSorted k m).denote ctx = ctx.add (p.denote ctx) (ctx.mul (ctx.ofInt k) (m.denote ctx)) := by
  match p with
  | [] => simp! [add_zero, zero_add]
  | (k', m') :: p =>
    by_cases h : m < m' <;> simp! [h, denote_insertSorted ctx k m p, add_assoc, add_comm, add_left_comm]

theorem Poly.mulMon_denote (ctx : Context α) (p : Poly) (k : Int) (m : Mon) : (p.mulMon k m).denote ctx = ctx.mul (p.denote ctx) (ctx.mul (ctx.ofInt k) (m.denote ctx)) := by
  simp [mulMon, go]; simp! [zero_add]
where
  go (p : Poly) (acc : Poly) : (mulMon.go k m p acc).denote ctx = ctx.add (acc.denote ctx) (ctx.mul (p.denote ctx) (ctx.mul (ctx.ofInt k) (m.denote ctx))) := by
   match p with
   | [] => simp! [zero_mul, add_zero]
   | (k', m') :: p =>
     simp! [go p, ofInt_mul, left_dist, denote_insertSorted, Mon.mul_denote, mul_assoc, mul_comm, mul_left_comm, add_assoc]

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

theorem Poly.neg_denote (ctx : Context α) (p : Poly) : p.neg.denote ctx = ctx.mul (ctx.ofInt (-1)) (p.denote ctx) := by
  match p with
  | [] => simp! [mul_zero]
  | (k, m) :: p => simp! [left_dist, ofInt_mul, neg_denote ctx p, mul_assoc, mul_comm, mul_left_comm]

theorem Expr.toPoly_denote (ctx : Context α) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    · simp [eq_of_beq h]; rfl
    · simp [mul_one, add_zero]
  | var v => simp! [mul_one, one_mul, add_zero]
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]
  | sub a b => simp! [Poly.add_denote, *, sub_def, Poly.neg_denote, mul_one, mul_comm]

theorem Expr.eq_of_toPoly_eq (ctx : Context α) (a b : Expr) (h : a.toPoly == b.toPoly) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [toPoly_denote] at h
  assumption

def ex1 : Expr := .mul (.add (.var 0) (.var 1)) (.add (.add (.var 0) (.var 1)) (.num 1))
def ex2 : Expr := .add (.mul (.var 0) (.add (.add (.num 1) (.var 1)) (.var 0)))
                       (.mul (.add (.add (.var 1) (.num 1)) (.var 0)) (.var 1))

#eval Expr.toPoly ex1
#eval Expr.toPoly ex2
