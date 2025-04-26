import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
open Lean.Grind.CommRing

def w : Expr := .var 0
def x : Expr := .var 1
def y : Expr := .var 2
def z : Expr := .var 3

instance : Add Expr where
  add a b := .add a b
instance : Sub Expr where
  sub a b := .sub a b
instance : Neg Expr where
  neg a := .neg a
instance : Mul Expr where
  mul a b := .mul a b
instance : HPow Expr Nat Expr where
  hPow a k := .pow a k
instance : OfNat Expr n where
  ofNat := .num n

def spol' (p₁ p₂ : Poly) : Poly :=
  p₁.spol p₂ |>.spol

def check_spoly (e₁ e₂ r : Expr) : Bool :=
  let p₁ := e₁.toPoly
  let p₂ := e₂.toPoly
  let r  := r.toPoly
  let s  := p₁.spol p₂
  spol' p₁ p₂ == r &&
  spol' p₂ p₁ == r.mulConst (-1) &&
  s.spol == r &&
  r == (p₁.mulMon s.c₁ s.m₁).combine (p₂.mulMon s.c₂ s.m₂)

example : check_spoly (y^2 - x + 1) (x*y - 1 + y) (-x^2 + y + x - y^2) := by native_decide
example : check_spoly (y - z + 1) (x*y - 1) (-x*z + 1 + x) := by native_decide
example : check_spoly (z^3 - x*y) (z*y - 1) (z^2 - x*y^2) := by native_decide
example : check_spoly (x + 1) (z + 1) (z - x) := by native_decide
example : check_spoly (w^2*x - y) (w*x^2 - z) (-y*x + z*w) := by native_decide
example : check_spoly (2*z^3 - x*y) (3*z*y - 1) (2*z^2 - 3*x*y^2) := by native_decide
example : check_spoly (2*x + 3) (3*z + 1) (9*z - 2*x) := by native_decide

example : check_spoly (2*y^2 - x + 1) (2*x*y - 1 + y) (-x^2 + y + x - y^2) := by native_decide
example : check_spoly (2*y^2 - x + 1) (4*x*y - 1 + y) (-2*x^2 + y + 2*x - y^2) := by native_decide
example : check_spoly (6*y^2 - x + 1) (4*x*y - 1 + y) (-2*x^2 + 3*y + 2*x - 3*y^2) := by native_decide

def simp? (p₁ p₂ : Poly) : Option Poly :=
  (·.p) <$> p₁.simp? p₂

partial def simp' (p₁ p₂ : Poly) : Poly :=
  if let some r := p₁.simp? p₂ then
    assert! r.p == (p₂.mulMon r.k₂ r.m₂).combine (p₁.mulConst r.k₁)
    simp' r.p p₂
  else
    p₁

def check_simp' (e₁ e₂ r : Expr) : Bool :=
  r.toPoly == simp' e₁.toPoly e₂.toPoly

example : check_simp' (x^2*y - 1) (x*y - y) (y - 1) := by native_decide
example : check_simp' (x^2 + x + 1) (2*x + 1) 3 := by native_decide
example : check_simp' (3*x^2 + x + y + 1) (2*x + 1) (4*y + 5) := by native_decide
example : check_simp' (3*x^2 + x + y + 1) (2*x + y) (3*y^2 + 2*y + 4) := by native_decide
example : check_simp' (z^4 + w^3 + x^2 + x + 1) (2*x + 1) (4*z^4 + 4*w^3 + 3) := by native_decide
