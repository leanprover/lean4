/-!
# Regression tests for isInstance changes in congruence lemma generation

These tests verify that `congr` works correctly for structures and classes
with class-typed fields. They catch regressions from changes to how instance
parameters are detected (e.g., using `isClass?` instead of binder info).

Both tests pass on v4.28.0-rc1 (before the isInstance changes).

## Test 1: Structure extending classes (mirrors Mathlib's GroupTopology)

When a structure extends both a data class and a Prop class, the parent class
field may be marked as `isInstance = true`. If this causes `.fixed` treatment
in congruence lemma generation, dependent Prop fields will require HEq.

**Failure mode:** `⊢ toIsContinuousMul✝¹ ≍ toIsContinuousMul✝`

## Test 2: Class with explicit class-typed field (mirrors Mathlib's PseudoEMetricSpace)

When a class has an explicit class-typed field (not from `extends`), that field
may be marked as `isInstance = true`. If this causes `.fixed` treatment, then
dependent Prop fields whose types mention that field will require HEq.

**Failure mode:** `⊢ dist_self✝¹ ≍ dist_self✝` and `⊢ uniformity_dist✝¹ ≍ uniformity_dist✝`
-/

/-! ### Test 1: Structure extending classes -/

-- Setup: mimic Mathlib's GroupTopology structure
class MyTopology (α : Type) where
  isOpen : (α → Prop) → Prop

-- A Prop-valued class that depends on MyTopology
class IsContinuousMul (α : Type) [MyTopology α] : Prop where
  continuous_mul : True  -- simplified

-- Structure extending both a data class and a Prop class
structure MyGroupTopology (α : Type) extends MyTopology α, IsContinuousMul α

-- Key test: proving injectivity of the parent projection using `congr`
-- If the toMyTopology field gets `.fixed` treatment, the Prop-valued
-- toIsContinuousMul field will require HEq: `⊢ toIsContinuousMul✝¹ ≍ toIsContinuousMul✝`
theorem MyGroupTopology.toMyTopology_injective {α : Type} :
    Function.Injective (MyGroupTopology.toMyTopology : MyGroupTopology α → MyTopology α) := by
  intro f g h
  cases f
  cases g
  congr

/-! ### Test 2: Class with explicit class-typed field -/

-- Setup: mimic Mathlib's PseudoEMetricSpace pattern
-- A class that extends one class but has another class-typed field explicitly

class MyDist (α : Type) where
  dist : α → α → Nat

class MyUniformity (α : Type) where
  uniformity : (α → α → Prop) → Prop

-- Class that extends MyDist but has an explicit MyUniformity field
-- This mirrors PseudoEMetricSpace which extends EDist but has explicit toUniformSpace
class MyMetricSpace (α : Type) extends MyDist α where
  dist_self : ∀ x : α, dist x x = 0
  -- Explicit class-typed field (NOT from extends)
  toMyUniformity : MyUniformity α
  -- Prop field whose type depends on toMyUniformity
  uniformity_dist : toMyUniformity.uniformity (fun x y => dist x y = 0)

-- Key test: extensionality theorem using `congr`
-- If toMyUniformity gets `.fixed` treatment (because it's class-typed but not
-- a subobject field), then `congr` will produce HEq goals for dependent fields
protected theorem MyMetricSpace.ext {α : Type} {m m' : MyMetricSpace α}
    (h : m.toMyDist = m'.toMyDist) (hU : m.toMyUniformity = m'.toMyUniformity) : m = m' := by
  cases m
  cases m'
  -- After cases, we need to prove the constructors are equal
  -- `congr` should produce goals for data fields (dist, toMyUniformity)
  -- and automatically handle Prop fields (dist_self, uniformity_dist) via casting
  -- If toMyUniformity gets `.fixed` treatment, we'd see HEq goals like:
  --   `⊢ dist_self✝¹ ≍ dist_self✝` or `⊢ uniformity_dist✝¹ ≍ uniformity_dist✝`
  congr 1 <;> assumption
