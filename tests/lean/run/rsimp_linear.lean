import Std.Tactic.RSimp
import Std.Tactic.RSimp.ConvTheorem

import Lean

namespace Data

/-!
A data structure for modelling `Fin n → α` (or `Array α`) optimized for a fast kernel-reduction get
operation.

For now not universe-polymorphic; smaller proof objects and no complication with the `ToExpr` type
class.
-/

inductive RArray (α : Type) : Type  where
  | leaf : α → RArray α
  | branch : Nat → RArray α → RArray α → RArray α

variable {α : Type}

/-- The crucial operation, written with very little abstractional overhead -/
noncomputable def RArray.get (a : RArray α) (n : Nat) : α :=
  RArray.rec (fun x => x) (fun p _ _ l r => (Nat.ble p n).rec l r) a

theorem RArray.get_eq_def (a : RArray α) (n : Nat) :
  a.get n = match a with
    | .leaf x => x
    | .branch p l r => (Nat.ble p n).rec (l.get n) (r.get n) := by
  conv => lhs; unfold RArray.get
  split <;> rfl

def RArray.getImpl (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.getImpl n else r.getImpl n

@[csimp]
theorem RArray.get_eq_getImpl : @RArray.get = @RArray.getImpl := by
  ext α a n
  induction a with
  | leaf _ => rfl
  | branch p l r ihl ihr =>
    rw [RArray.getImpl, RArray.get_eq_def]
    simp only [ihl, ihr]
    cases hnp : Nat.ble p n
    · replace hnp := ne_true_of_eq_false hnp
      simp at hnp
      rw [if_pos]
      omega
    · simp at hnp
      rw [if_neg]
      omega

instance : GetElem (RArray α) Nat α (fun _ _ => True) where
  getElem a n _ := a.get n

def RArray.size : RArray α → Nat
  | leaf _ => 1
  | branch _ l r => l.size + r.size

def RArray.ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) : RArray α :=
  go 0 n h (Nat.le_refl _)
where
  go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ n) : RArray α :=
    if h : lb + 1 = ub then
      .leaf (f ⟨lb, Nat.lt_of_lt_of_le h1 h2⟩)
    else
      let mid := (lb + ub)/2
      .branch mid (go lb mid (by omega) (by omega)) (go mid ub (by omega) h2)

def RArray.ofArray (xs : Array α) (h : 0 < xs.size) : RArray α :=
  .ofFn (fun i => xs.get i) h

theorem RArray.ofFn_correct {n : Nat} (f : Fin n → α) (h : 0 < n) (i : Fin n):
    RArray.get (.ofFn f h) i = f i :=
  go 0 n h (Nat.le_refl _) (Nat.zero_le _) i.2
where
  go lb ub h1 h2 (h3 : lb ≤ i.val) (h3 : i.val < ub) : RArray.get (.ofFn.go f lb ub h1 h2) i = f i := by
    induction lb, ub, h1, h2 using RArray.ofFn.go.induct (f := f) (n := n)
    case case1 =>
      simp [ofFn.go, RArray.get_eq_getImpl, RArray.getImpl]
      congr
      omega
    case case2 ih1 ih2 hiu =>
      rw [ofFn.go]; simp only [↓reduceDIte, *]
      simp [RArray.get_eq_getImpl, RArray.getImpl] at *
      split
      · rw [ih1] <;> omega
      · rw [ih2] <;> omega


section Meta
open Lean

def RArray.toExpr (ty : Expr) (f : α → Expr) : RArray α → Expr
  | .leaf x       =>
    mkApp2 (mkConst ``RArray.leaf) ty (f x)
  | .branch p l r =>
    mkApp4 (mkConst ``RArray.branch) ty (.lit (.natVal p)) (l.toExpr ty f) (r.toExpr ty f)

instance [ToExpr α] : ToExpr (RArray α) where
  toExpr a := a.toExpr (toTypeExpr α) (toExpr ·)
  toTypeExpr := mkApp (mkConst ``RArray) (toTypeExpr α)

end Meta
end Data

open Nat.Linear

section sortFuse

-- Oddly, fusing norm and fuse does not yield a speed-up

def Nat.Linear.Poly.insertSortedFused (k : Nat) (v : Var) (p : Poly) : Poly :=
  match p with
  | [] => [(k, v)]
  | (k', v') :: p =>
    bif Nat.blt v v' then
      (k, v) :: (k', v') :: p
    else
      bif Nat.beq v v' then
        (k + k', v) :: p
      else
        (k', v') :: insertSortedFused k v p

def Nat.Linear.Poly.sortFuse (p : Poly) : Poly :=
  let rec go (p : Poly) (r : Poly) : Poly :=
    match p with
    | [] => r
    | (k, v) :: p => go p (r.insertSortedFused k v)
  go p []

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Nat.Linear.Poly.norm_eq_sortFuse (p : Poly) : p.norm = p.sortFuse := by
  sorry

end sortFuse

section ToPoly

def Nat.Linear.Expr.toPolyAux (coeff : Nat) : Expr → (Poly → Poly)
  | Expr.num k    => bif k == 0 then id else ((coeff * k, fixedVar) :: ·)
  | Expr.var i    => ((coeff, i) :: ·)
  | Expr.add a b  => a.toPolyAux coeff ∘ b.toPolyAux coeff
  | Expr.mulL k a => if k == 0 then id else a.toPolyAux (k * coeff)
  | Expr.mulR a k => if k == 0 then id else a.toPolyAux (k * coeff)

-- attribute [rsimp_optimize] Nat.Linear.Expr.toPoly

noncomputable
def Nat.Linear.Expr.toPolyFast (e : Expr) : Poly :=
  Nat.Linear.Expr.toPolyAux 1 e []

@[simp]
theorem Nat.Linear.Poly.mul.go_append :
    Nat.Linear.Poly.mul.go k (p₁ ++ p₂) =
    Nat.Linear.Poly.mul.go k p₁ ++ Nat.Linear.Poly.mul.go k p₂ := by
  induction p₁ <;> simp [mul.go, *]

@[simp]
theorem Nat.Linear.Poly.mul_nil :
    Nat.Linear.Poly.mul k [] = [] := by simp [mul, mul.go]

@[simp]
theorem Nat.Linear.Poly.mul_0 :
    Nat.Linear.Poly.mul 0 p = [] := by simp [mul]

@[simp]
theorem Nat.Linear.Poly.mul_append :
    Nat.Linear.Poly.mul k (p₁ ++ p₂) =
    Nat.Linear.Poly.mul k p₁ ++ Nat.Linear.Poly.mul k p₂ := by
  unfold Poly.mul
  simp only [cond_eq_if]
  split <;> (try split) <;> simp

@[simp]
theorem Nat.Linear.Poly.mul_go_mul_go :
    Poly.mul.go k (Poly.mul.go k' p) = Poly.mul.go (k * k') p := by
  induction p <;> simp_all [mul.go, Nat.mul_assoc]

theorem Nat.mul_eq_one (n m : Nat) : n * m = 1 ↔ (n = 1 ∧ m = 1) := by
  cases n <;> simp
  rename_i n
  cases m <;> simp
  rename_i m
  cases n <;> simp
  rename_i n
  simp [Nat.mul_add, ← Nat.add_assoc]


@[simp]
theorem Nat.Linear.Poly.mul_mul :
  Poly.mul k (Poly.mul k' p) = Poly.mul (k' * k) p := by
  unfold Poly.mul
  simp only [cond_eq_if, beq_iff_eq, Nat.mul_eq_one, Nat.mul_eq_zero]
  repeat' split <;> try (simp_all [mul.go, Nat.mul_comm])

theorem Nat.Linear.Expr.toPoly_eq_toPolyFast :
  Nat.Linear.Expr.toPoly = Nat.Linear.Expr.toPolyFast := by
  funext p
  unfold toPolyFast
  suffices ∀ k r, k ≠ 0 → (p.toPoly.mul k ++ r = toPolyAux k p r) by simpa using this 1 []
  intro k r hk
  induction p generalizing k r
  · simp [toPoly, toPolyAux, cond_eq_if, hk]
    split
    . simp [Poly.mul, Poly.mul.go]
    . simp [Poly.mul, Poly.mul.go, cond_eq_if, *]
      split <;> simp [*]
  · simp [toPoly, toPolyAux, cond_eq_if, Poly.mul, Poly.mul.go, hk]
    split <;> simp [*]
  next iha ihb =>
    simp [toPoly, toPolyAux, cond_eq_if, hk]
    rw [← ihb k _ hk, ← iha k _ hk]
  next k' _ ih =>
    simp [toPoly, toPolyAux, cond_eq_if, hk]
    split
    · simp [*]
    · rw [← ih (k' * k) _ _]
      simp [*, Nat.mul_ne_zero]
  next _ k' ih =>
    simp [toPoly, toPolyAux, cond_eq_if, hk]
    split
    · simp [*]
    · rw [← ih (k' * k) _ _]
      simp [*, Nat.mul_ne_zero]

end ToPoly

section AltDenote

def Nat.Linear.Expr.denote' (ctx : Data.RArray Nat) : Expr → Nat
  | Expr.add a b  => Nat.add (denote' ctx a) (denote' ctx b)
  | Expr.num k    => k
  | Expr.var v    => ctx.get v
  | Expr.mulL k e => Nat.mul k (denote' ctx e)
  | Expr.mulR e k => Nat.mul (denote' ctx e) k

end AltDenote

-- theorem Nat.beq_eq' (a b : Nat) : (a == b) = Nat.beq a b := sorry

attribute [rsimp ←] Nat.beq_eq Nat.mul_eq Nat.add_eq Bool.cond_decide
attribute [rsimp] Std.Tactic.BVDecide.Normalize.Bool.decide_eq_true
attribute [rsimp] BEq.beq
attribute [rsimp_optimize] Nat.Linear.Poly.mul.go
attribute [rsimp_optimize] Nat.Linear.Poly.mul

attribute [rsimp_optimize] Nat.Linear.Poly.insertSortedFused
attribute [rsimp_optimize] Nat.Linear.Poly.sortFuse.go
attribute [rsimp_optimize] Nat.Linear.Poly.sortFuse

attribute [rsimp_optimize] Nat.Linear.Poly.insertSorted
attribute [rsimp_optimize] Nat.Linear.Poly.sort.go
attribute [rsimp_optimize] Nat.Linear.Poly.sort
attribute [rsimp_optimize] Nat.Linear.Poly.fuse
attribute [rsimp_optimize] Nat.Linear.Expr.toPolyAux
attribute [rsimp_optimize] Nat.Linear.Expr.toPolyFast

-- This is actually a bit slower, it seems
-- But faster if there are repeated variables
attribute [rsimp] Nat.Linear.Poly.norm_eq_sortFuse
-- attribute [rsimp_optimize] Nat.Linear.Poly.norm


-- attribute [rsimp_optimize] Nat.Linear.Expr.toPoly
attribute [rsimp] Nat.Linear.Expr.toPoly_eq_toPolyFast

attribute [rsimp_optimize] Nat.Linear.Expr.toNormPoly
attribute [rsimp ←] List.reverseAux_eq
attribute [rsimp_optimize] Nat.Linear.Poly.cancelAux
attribute [rsimp_optimize] Nat.Linear.Poly.cancel

attribute [rsimp_optimize] Nat.Linear.Var.denote.go
attribute [rsimp_optimize] Nat.Linear.Var.denote
-- set_option trace.tactic.rsimp_optimize true in
attribute [rsimp_optimize] Nat.Linear.Expr.denote

/-- A hook to use below, and to easily swap out the definition -/
def Nat.Linear.Expr.toPoly' := @Nat.Linear.Expr.toPoly

theorem Nat.Linear.Expr.toPoly'_eq_to_Poly :
  Nat.Linear.Expr.toPoly = Nat.Linear.Expr.toPoly' := rfl
-- set_option trace.tactic.rsimp_optimize true in
attribute [rsimp_optimize] Nat.Linear.Expr.toPoly'

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Nat.Linear.Expr.of_cancel_eq_no_rfl (ctx : Context) (a b c d : Expr) :
  (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) := sorry

theorem Nat.Linear.Expr.of_cancel_eq_opt (ctx : Context) (a b c d : Expr)
  (h : Poly.cancel.rsimp (Expr.toNormPoly.rsimp a) (Expr.toNormPoly.rsimp b) =
    (Expr.toPoly'.rsimp c, Expr.toPoly'.rsimp d)) :
  (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) := by
  revert h
  simp only [← Expr.toNormPoly.eq_rsimp, ← Expr.toPolyFast.eq_rsimp,
    ← Poly.cancel.eq_rsimp, Nat.Linear.Expr.toPoly'_eq_to_Poly, ← toPoly'.eq_rsimp]
  exact Expr.of_cancel_eq ctx a b c d

theorem Nat.Linear.Expr.of_cancel_eq_opt_denote (ctx : Context) (a b c d : Expr)
  (h : Poly.cancel.rsimp (Expr.toNormPoly.rsimp a) (Expr.toNormPoly.rsimp b) =
    (Expr.toPolyFast.rsimp c, Expr.toPolyFast.rsimp d)) :
  (Nat.Linear.Expr.denote.rsimp ctx a = Nat.Linear.Expr.denote.rsimp ctx b) =
  (Nat.Linear.Expr.denote.rsimp ctx c = Nat.Linear.Expr.denote.rsimp ctx d) := by
  revert h
  simp only [← Expr.toNormPoly.eq_rsimp, ← Expr.toPolyFast.eq_rsimp,
    ← Poly.cancel.eq_rsimp, ← Nat.Linear.Expr.toPoly_eq_toPolyFast,
    ← Nat.Linear.Expr.denote.eq_rsimp
    ]
  exact Expr.of_cancel_eq ctx a b c d

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Nat.Linear.Expr.of_cancel_eq_opt_denote' (ctx : Data.RArray Nat) (a b c d : Expr)
  (h : Poly.cancel.rsimp (Expr.toNormPoly.rsimp a) (Expr.toNormPoly.rsimp b) = (Expr.toPolyFast.rsimp c, Expr.toPolyFast.rsimp d)) :
  (Nat.Linear.Expr.denote' ctx a = Nat.Linear.Expr.denote' ctx b) =
  (Nat.Linear.Expr.denote' ctx c = Nat.Linear.Expr.denote' ctx d) := by
  sorry
  all_goals
  revert h
  simp only [← Expr.toNormPoly.eq_rsimp, ← Expr.toPolyFast.eq_rsimp,
    ← Poly.cancel.eq_rsimp, ← Nat.Linear.Expr.toPoly_eq_toPolyFast,
    ← Nat.Linear.Expr.denote.eq_rsimp
    ]
  exact Expr.of_cancel_eq ctx a b c d

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem Nat.Linear.Expr.of_cancel_eq_opt_denote'_no_rfl (ctx : Data.RArray Nat) (a b c d : Expr)
  (h : True) :
  (Nat.Linear.Expr.denote' ctx a = Nat.Linear.Expr.denote' ctx b) =
  (Nat.Linear.Expr.denote' ctx c = Nat.Linear.Expr.denote' ctx d) := by
  sorry

open Lean Meta

def bench (variant : Nat) : MetaM Unit :=
  let n := 40
  let decls := Array.ofFn fun (i : Fin n) => ((`x).appendIndexAfter i, (fun _ => pure (mkConst ``Nat)))
  withLocalDeclsD decls fun xs => do
    if h : 0 < xs.size then
      let mut e₁ := Expr.num 42
      let mut e₂ := Expr.num 23
      for _ in [:4] do
        for i in [:xs.size] do
          e₁ := .add (.mulL i e₁) (.var i)
          e₂ := .add (.var i) (Expr.mulR e₂ (xs.size - i))

      let (p₁', p₂') := Poly.cancel e₁.toNormPoly e₂.toNormPoly
      let e₁' := p₁'.toExpr
      let e₂' := p₂'.toExpr
      have _value_orig := mkApp6 (.const ``Expr.of_cancel_eq [])
        (← mkListLit (mkConst ``Nat) xs.toList)
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
        (← mkEqRefl (toExpr (p₁', p₂')))
      have _value_no_rfl := mkApp5 (.const ``Expr.of_cancel_eq_no_rfl [])
        (← mkListLit (mkConst ``Nat) xs.toList)
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
      have _value_opt := mkApp6 (.const ``Expr.of_cancel_eq_opt [])
        (← mkListLit (mkConst ``Nat) xs.toList)
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
        (← mkEqRefl (toExpr (p₁', p₂')))
      have _value_opt_denote := mkApp6 (.const ``Expr.of_cancel_eq_opt_denote [])
        (← mkListLit (mkConst ``Nat) xs.toList)
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
        (← mkEqRefl (toExpr (p₁', p₂')))
      have _value_opt_denote' := mkApp6 (.const ``Expr.of_cancel_eq_opt_denote' [])
        (Data.RArray.toExpr (mkConst ``Nat) id (.ofArray xs h))
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
        (← mkEqRefl (toExpr (p₁', p₂')))
      have _value_opt_denote'_no_rfl := mkApp6 (.const ``Expr.of_cancel_eq_opt_denote'_no_rfl [])
        (Data.RArray.toExpr (mkConst ``Nat) id (.ofArray xs h))
        (toExpr e₁) (toExpr e₂) (toExpr e₁') (toExpr e₂')
        (mkConst ``True.intro)
      let value := match variant with
        | 0 => _value_orig
        | 1 => _value_no_rfl
        | 2 => _value_opt
        | 3 => _value_opt_denote
        | 4 => _value_opt_denote'
        | _ => _value_opt_denote'_no_rfl
      let value ← mkLambdaFVars xs value
      let exp₁ ← Linear.Nat.LinearExpr.toArith xs e₁
      let exp₂ ← Linear.Nat.LinearExpr.toArith xs e₂
      let exp₁' ← Linear.Nat.LinearExpr.toArith xs e₁'
      let exp₂' ← Linear.Nat.LinearExpr.toArith xs e₂'
      let type ← mkEq (← mkEq exp₁ exp₂) (← mkEq exp₁' exp₂')
      let type ← mkForallFVars xs type

      let name := `linear_test
      let decl := .thmDecl { name, value, type, levelParams := [] }
      let timings : List Nat ← (List.range 5).mapM fun _ =>
        withoutModifyingEnv do
          let start ← IO.monoMsNow
          addDecl decl
          return (← IO.monoMsNow) - start
      let some best := timings.min? | unreachable!
      logInfo m!"time {variant}: {best}ms"
      -- logInfo m!"{type}"
    else
      unreachable!

-- run_meta bench 0
-- run_meta bench 1
run_meta bench 2
run_meta bench 3
run_meta bench 4
run_meta bench 5
