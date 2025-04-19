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

def check_spoly (e₁ e₂ r : Expr) : Bool :=
  e₁.toPoly.superpose e₂.toPoly == r.toPoly &&
  e₂.toPoly.superpose e₁.toPoly == (-r).toPoly

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
