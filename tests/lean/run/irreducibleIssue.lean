class Trait (X : Type u) where
  R : Type v

attribute [reducible] Trait.R

class SemiInner (X : Type u) (R : Type v) where
  semiInner : X → X → R

@[reducible] instance (X) (R : Type u) [SemiInner X R] : Trait X := ⟨R⟩

def norm {X} [Trait X] [inst : SemiInner X (Trait.R X)] (x : X) : Trait.R X := SemiInner.semiInner x x

section Real
  def ℝ := Float
  instance : SemiInner ℝ ℝ := ⟨λ x y : Float => x * y⟩

  attribute [irreducible] ℝ

  variable (x : ℝ)
  #check (norm x : ℝ)
