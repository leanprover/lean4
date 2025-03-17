class Vec (X : Type u)

class IsLin {X Y} [Vec X] [Vec Y] (f : X → Y)

structure ℝ where
  value : Float

instance instFoo1 {X : Type u} {Y : Type v} [Vec X] [Vec Y] : Vec (X × Y) := sorry
instance instProblem {α : Type u} {X : Type v} [Vec X] : Vec (α → X) := sorry

instance (priority := default+1) instFoo2 : Vec ℝ := sorry

--------------

instance comp_is_lin {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) (g : X → Y) [IsLin f] [IsLin g]
  : IsLin (λ x => f (g x)) := sorry

----------------

class Trait (X : Type u) where
  R : Type v

attribute [reducible] Trait.R

class SemiInner (X : Type u) (R : outParam (Type v)) where
  semiInner : X → X → R

@[reducible] instance (X) (R : Type u) [SemiInner X R] : Trait X := ⟨R⟩

class SemiHilbert (X) (R : outParam (Type u)) [Vec R] [Vec X] extends SemiInner X R

instance (X R) [Trait X] [Vec R] [Vec X] [SemiHilbert X R] (ι : Type v) : SemiHilbert (ι → X) R := sorry
instance : SemiHilbert ℝ ℝ := sorry

--------------

def norm {X} [Trait X] [inst : SemiInner X (Trait.R X)] (x : X) : Trait.R X := sorry
def sum {n} (f : Fin n → ℝ) : ℝ := sorry

variable (n m : Nat)

-- these all should work
example : Trait (Fin n → Fin m → ℝ) := by infer_instance
example : SemiInner ℝ (Trait.R ℝ) := by infer_instance
example : SemiHilbert (Fin n → ℝ) ℝ := by infer_instance
example : SemiHilbert (Fin n → ℝ) (Trait.R ℝ) := by infer_instance
example : Trait (Fin n → Fin m → (Trait.R ℝ)) := by infer_instance
example : SemiHilbert (Trait.R ℝ) ℝ := by infer_instance

-- set_option synthInstance.maxHeartbeats 50 in
-- set_option pp.explicit true in
-- set_option trace.Meta.synthInstance true in

-- This should not timeout but fail in finite number of steps like in Lean 3
example : IsLin  (λ (x : ℝ) => sum λ i : Fin n => norm x) := by infer_instance
