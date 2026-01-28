/-
Regression test for https://github.com/leanprover/lean4/pull/12172

The pattern:
1. A class `MeasurableSpace` is used as both a class and explicit argument (via @)
2. `Measure.trim` takes a Prop proof `hm : m ≤ m0` and returns `@Measure α m`
3. A typeclass `SigmaFinite` depends on `μ.trim hm`
4. A function `myFun` has `hm` explicit and `[SigmaFinite (μ.trim hm)]` as instance
5. A section variable makes `hm` implicit
6. A lemma `myFun_eq` takes an explicit proof argument before the final arg

When calling `simp only [myFun_eq μ hs]`:
- Before #12172: `hm` is inferred, instance is found, works
- After #12172: Instance synthesis happens before `hm` is inferred, fails with
  "failed to synthesize instance SigmaFinite (μ.trim ?m.XX)"

Workaround: `simp only [myFun_eq (hm := hm) μ hs]`

This pattern is used in Mathlib's MeasureTheory.Function.ConditionalExpectation.CondexpL1
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

class MeasurableSpace (α : Type u) where
  dummy : Unit := ()

instance {α : Type u} : LE (MeasurableSpace α) where
  le _ _ := True

structure Measure (α : Type u) [MeasurableSpace α] where
  val : Nat

def Measure.trim {α : Type u} {m m0 : MeasurableSpace α}
    (μ : @Measure α m0) (_hm : m ≤ m0) : @Measure α m :=
  @Measure.mk α m μ.val

class SigmaFinite {α : Type u} {m0 : MeasurableSpace α} (_μ : @Measure α m0) : Prop where
  sigma_finite : True

def myFun {α : Type u} {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : @Measure α m0)
    [SigmaFinite (μ.trim hm)] (n : Nat) : Nat := n

section
variable {α : Type u} {m m0 : MeasurableSpace α}
variable (μ : @Measure α m0)
variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)] {s : Nat}

theorem myFun_eq (hs : s > 0) (n : Nat) : myFun hm μ n = n := rfl

-- This should work (worked before #12172)
theorem test_implicit_hm (hs : s > 0) (x y : Nat) :
    myFun hm μ (x + y) = myFun hm μ x + myFun hm μ y := by
  simp only [myFun_eq μ hs]

-- Workaround with explicit hm also works
theorem test_explicit_hm (hs : s > 0) (x y : Nat) :
    myFun hm μ (x + y) = myFun hm μ x + myFun hm μ y := by
  simp only [myFun_eq (hm := hm) μ hs]

end
