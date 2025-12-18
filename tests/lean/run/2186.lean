/-!
# Regression tests for #2186

https://github.com/leanprover/lean4/issues/2186
-/

/-!
Minimization of the issue. The default value to `bar` wasn't working
because the default value of `bar` was `fun (_ : p) => trivial`,
and `p` (which in the default value itself appears as a projection) wasn't being reduced.
-/
namespace Test1

structure A (α : Type u) where
  p : Prop
  bar : p → True

structure B (α : Type _) extends A α where
  bar _ := trivial

-- Previously this needed `bar` to be specified
example : B α where
  p := False

end Test1

/-!
Tests from the issue.
-/
namespace Test2
variable (α : Type _)

-- First example
structure A extends LE α where
  foo : True
structure B extends LE α where
  bar : ∀ a b : α, a ≤ b → True
structure C extends A α, B α

structure D extends C α where
  foo := trivial
structure E extends C α where
  bar _ _ _ := trivial

-- Always worked
example : D α where
  le := Eq
  bar _ _ _ := trivial
-- Didn't work
example : E α where
  le := Eq
  foo := trivial

-- Second example
structure X where
  transform : α → α

structure A₁ extends X α where
  foo : True
structure B₁ extends X α where
  bar : ∀ a, transform a = transform (transform a) → True
structure C₁ extends A₁ α, B₁ α

structure D₁ extends C₁ α where
  foo := trivial
structure E₁ extends C₁ α where
  bar _ _ := trivial

-- Always worked
example : D₁ α where
  transform := id
  bar := fun _ _ => trivial
-- Didn't work
example : E₁ α where
  transform := id
  foo := trivial

end Test2
