open Lean.Grind.CommRing

def w : Var := 0
def x : Var := 1
def y : Var := 2
def z : Var := 3

macro:100 (priority:=high) a:ident "^" k:num : term => `(Power.mk $a $k)
infixr:70 (priority:=high) "." => Mon.cons
instance : Coe Power Mon where
  coe p := Mon.leaf p
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
