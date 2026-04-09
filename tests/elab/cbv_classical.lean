/-!
# A regression test against `cbv` picking up `Classical.propDecidable`,
when re-synthesizing instances.

When `cbv` encounters `decide P`, it simplifies the proposition `P`. If `P`
unfolds (e.g. `IsEven 2` → `∃ k, 2 * k = 2`), `simpDecideCbv` tries to
synthesize `Decidable` instance for the *unfolded* form. With `open Classical`,
this was picking up `Classical.propDecidable` (which uses `choice`), replacing
the original computable instance with one that cannot be evaluated.

The code now contains a guard ensuring that the instance is not made of constants
marked as `noncomputable`.
-/

-- A predicate wrapping an existential — has a computable `DecidablePred` instance,
-- but the unfolded existential has none (except the classical one).
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

instance : DecidablePred IsEven := fun n =>
  if h : n % 2 = 0 then
    .isTrue ⟨n / 2, by omega⟩
  else
    .isFalse (by intro ⟨k, hk⟩; omega)


-- Works, using the provided `DecidablePred` instance.
example : decide (IsEven 2) = true := by cbv

example : decide (IsEven 3) = false := by cbv

-- Should not fail, when `Classical.propDecidable` becomes available.
open Classical in
example : decide (IsEven 2) = true := by cbv

open Classical in
example : decide (IsEven 3) = false := by cbv
