/-!
Equation lemmas for a `match` whose compiled matcher cases on a discriminant that the
alternative leaves variable.

The objects `WI` extend `Nat` by an initial object `star`, and `x ⟶ y` is the terminal-object
`HomT y x` with swapped arguments. The match compiler discharges the alternatives with an empty
`Hom` itself, so for the last alternative of `tensorHom` the matcher cases on `y₁`. The statement
of `tensorHom.eq_6` comes from the matcher's congruence equation, and its proof rewrites with the
same equation.
-/

class Quiver (V : Type) where
  Hom : V → V → Type

infixr:10 " ⟶ " => Quiver.Hom

inductive WI where
  | of : Nat → WI
  | star : WI

namespace WI

/-- Morphisms of the terminal-object extension. -/
@[implicit_reducible] def HomT : WI → WI → Type
  | of _, of _ => Nat
  | star, of _ => PEmpty
  | _, star => PUnit

instance : Quiver WI where
  Hom x y := HomT y x

def fromStar : ∀ x : WI, star ⟶ x
  | of _ => PUnit.unit
  | star => PUnit.unit

def tensorObj : WI → WI → WI
  | of m, of n => of (m + n)
  | star, x => x
  | x, star => x

set_option linter.unusedVariables false in
def tensorHom {x₁ y₁ x₂ y₂ : WI} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObj x₁ x₂ ⟶ tensorObj y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => (Nat.add f₁ f₂ : Nat)
  | .of _, .of _, .star, .of _, f₁, _ => (f₁ : Nat)
  | .star, .of _, .of _, .of _, _, f₂ => (f₂ : Nat)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, x, .star, y, _, _ => fromStar (tensorObj x y)

end WI

/--
info: WI.tensorHom.eq_6 {y₁ y₂ : WI} (f₁ : WI.star ⟶ y₁) (f₂ : WI.star ⟶ y₂) : WI.tensorHom f₁ f₂ = (y₁.tensorObj y₂).fromStar
-/
#guard_msgs in
#check WI.tensorHom.eq_6
