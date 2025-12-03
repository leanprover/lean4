module
public import Init.Grind.Ring.CommSolver
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
open Lean.Grind.CommRing

def w : Var := 0
def x : Var := 1
def y : Var := 2
def z : Var := 3

macro:100 (priority:=high) a:ident "^" k:num : term => `(Power.mk $a $k)
infixr:70 (priority:=high) "." => Mon.mult
instance : Coe Power Mon where
  coe p := Mon.mult p .unit
instance : Coe Var Power where
  coe x := x^1

example : { x := x, k := 2 : Power} = x^2 := rfl

def check_revlex (m₁ m₂ : Mon) : Bool :=
  m₁.revlex m₁ == .eq &&
  m₂.revlex m₂ == .eq &&
  m₁.revlex m₂ == .lt &&
  m₂.revlex m₁ == .gt

example : check_revlex z y := rfl
example : check_revlex z x := rfl
example : check_revlex z w := rfl
example : check_revlex y x := rfl
example : check_revlex y w := rfl
example : check_revlex x w := rfl

example : check_revlex (x^2) x := rfl
example : check_revlex (x^100) x := rfl
example : check_revlex (x^100) (x^88) := rfl
example : check_revlex (z^100) z := rfl

example : check_revlex (w . x^2) (w^2 . x) := rfl
example : check_revlex (w . x^2 . y) (w^2 . x . y) := rfl
example : check_revlex (w^2 . x . z^2) (w^2 . x . y) := rfl
example : check_revlex (x^3 . y^2 . z) (w^1 . x^4 . y^1 . z) := rfl
example : check_revlex (x^3 . y^2 . z) (w^1 . x^4 . y^1) := rfl
example : check_revlex (x^3 . y^2 . z) (w^1 . x^4 . y^1) := rfl
example : check_revlex (w^4 . z) (w^3 . x^2) := rfl
example : check_revlex (w^3 . y) (w^2 . x^2) := rfl
example : check_revlex (w . x^2 . y) (w^4) := rfl
example : check_revlex (w^2 . y^2 . z) (w^2 . y^3) := rfl
example : check_revlex (w^2 . x . z^2) (w^3 . x . z) := rfl
example : Mon.revlex (w^2 . x . z^3) (w^2 . x . z^3) = .eq := rfl
example : check_revlex (w . x^2 . z^5) (w . x^2 . z^2) := rfl
example : check_revlex (w . z^2) (w^10 . x^5 . y^3 . z) := rfl
example : check_revlex (w^2 . x^2 . y) (w^2 . x^2) := rfl
example : check_revlex (w^2 . x^2 . y) (w^2) := rfl
example : check_revlex (w^2 . x^2 . y) (x^2) := rfl
example : check_revlex (z) (w^8) := rfl
example : check_revlex (z) (x^100) := rfl
example : check_revlex (z^100) (z) := rfl
example : check_revlex (x^2 . y^2 . z^5) (x^2 . y^3 . z^4) := rfl

example : Mon.div (w^2 . y^2 . z) (w^2 . y) = y . z := rfl
example : Mon.div (w^2 . y^2 . z) y = w^2 . y . z := rfl
example : Mon.div (w^2 . y^2 . z) (y^2) = w^2 . z := rfl
example : Mon.div (w^2 . y^4) .unit = w^2 . y^4 := rfl
example : Mon.div (w^2 . y^4) (w^2 . y^4) = .unit := rfl
example : Mon.div (w^2 . y^4) (w^2 . y^5) = .unit := rfl
example : Mon.div (w^5) w = w^4 := rfl
example : Mon.div (w^5 . x^3 . y^2) (w^2 . x) = w^3 . x^2 . y^2 := rfl
example : Mon.div (y^2 . z^3) (y . z) = y . z^2 := rfl
example : Mon.div (x . y) (x . y) = .unit := rfl
example : Mon.div (w . x^2 . y) (w . x . y) = x := rfl

example : Mon.divides (x^2) (w^5) = false := rfl

def check_divides (m₁ m₂ : Mon) :=
  m₂.divides m₁ && (m₁ == m₂ || !m₁.divides m₂)

example : check_divides (w^5) w := rfl
example : check_divides (w^2 . y^2 . z) (w^2 . y) := rfl
example : check_divides (w^2 . y^2 . z) y := rfl
example : check_divides (w^2 . y^2 . z) (y^2) := rfl
example : check_divides (w^2 . y^4) .unit  := rfl
example : check_divides (w^2 . y^4) (w^2 . y^4) := rfl
example : check_divides (w^5) w := rfl
example : check_divides (w^5 . x^3 . y^2) (w^2 . x) := rfl
example : check_divides (x . y) (x . y) := rfl

#eval Mon.lcm Mon.unit (w^3 . y^2)

def check_lcm (m₁ m₂ r : Mon) :=
  m₁.lcm m₁ == m₁ &&
  m₂.lcm m₂ == m₂ &&
  m₁.lcm m₂ == r &&
  m₂.lcm m₁ == r

example : check_lcm (.unit) (w^3 . y^2) (w^3 . y^2) := by native_decide
example : check_lcm (w^3 . y^2) Mon.unit (w^3 . y^2) := by native_decide
example : check_lcm (w^2) (w^5) (w^5) := by native_decide
example : check_lcm x y (x . y) := by native_decide
example : check_lcm y z (y . z) := by native_decide
example : check_lcm (w^2 . x^3) (w^5 . x . y^2) (w^5 . x^3 . y^2) := by native_decide
example : check_lcm (w . x . y) z (w . x . y . z) := by native_decide
example : check_lcm (x^2 . y^3) (x^2 . y^5) (x^2 . y^5) := by native_decide
example : check_lcm (w^100 . x^2) (x^50 . y) (w^100 . x^50 . y) := by native_decide

def a : Var := 0
def b : Var := 1
def c : Var := 2

example : check_revlex (c) (a) := rfl
example : check_revlex (c) (a . b) := rfl
example : check_revlex (a . b . c) (c) := rfl
example : check_revlex (c) (b) := rfl
example : check_revlex (b) (a) := rfl
example : check_revlex (c^2) (c) := rfl
example : check_revlex (b . c) (a . c) := rfl
example : check_revlex (b . c) (c) := rfl
example : check_revlex (b^2 . c) (c) := rfl
example : check_revlex (a . c) (c) := rfl
example : check_revlex (a . b . c) (c) := rfl
example : check_revlex (a . b . c) (b . c) := rfl
example : check_revlex (a . b . c) (a . c) := rfl
example : check_revlex (a . b . c) (a . b) := rfl
example : check_revlex (a^2 . b . c) (a . b . c) := rfl
example : check_revlex (b . c) (b) := rfl
example : check_revlex (a . c) (a) := rfl
example : check_revlex (b) (a) := rfl
