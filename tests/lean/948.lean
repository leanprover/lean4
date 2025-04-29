class Trait (X : Type) where
  R : Type

attribute [reducible] Trait.R

def add_one {X} [Trait X] [One (Trait.R X)] [HAdd X (Trait.R X) X] (x : X) : X := x + (One.one : (Trait.R X))

@[reducible] instance : Trait Int := ⟨Nat⟩
instance : One Nat := ⟨1⟩
instance : HAdd Int Nat Int := ⟨λ x y => x + y⟩

def add_one_to_one (x : Int) (h : x = 1) : add_one (x : Int) = (2 : Int) := by
  conv =>
    pattern add_one _
    trace_state
    rw [h]
  rfl
