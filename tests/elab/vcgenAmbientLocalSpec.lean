import Std.Internal.Do
import Std.Tactic.Do

/-! `vcgen` ranks the specs available at a call site into priority bands: a spec named in the
`vcgen [...]` list outranks a local hypothesis pulled in by `*`, which outranks a spec collected
from an ambient hypothesis. The call-site bands sit just above `high`, so an `@[spec high]` used to
outrank default specs does not shadow a call-site spec, while a priority above the band still does.

`viaBinder`, `viaHave`, and `viaStar` prove one goal three ways, checking that a named spec wins over
the ambient spec collected from the same hypothesis. `namedBeatsSpec`, `specHighLoses`, and
`specHighestWins` isolate the banding against `@[spec]`, `@[spec high]`, and a priority above the band.
`unfoldBeatsSpec` checks that a bracketed definition is unfolded ahead of a lossy `@[spec]` keyed on
the same program, including when the program's state type is a variable.
-/

open Std.Internal.Do Lean.Order
set_option mvcgen.warning false
set_option linter.unusedVariables false

abbrev P := ExceptT String (StateM (List Char))

opaque enc : Nat → List Char

def item (fuel : Nat) : P Nat := do
  match ← get with
  | [] => throw "eof"
  | _ :: cs => set cs; pure fuel

def tail (fuel : Nat) (acc : Nat) : P Nat := do
  match ← get with
  | '+' :: cs =>
    match fuel with
    | 0 => throw "out of fuel"
    | fuel + 1 => set cs; let x ← item fuel; tail fuel (acc + x)
  | _ => pure acc

theorem tail_stop (rest : List Char) (fuel acc : Nat) (h : rest.head? ≠ some '+') :
    ⦃ fun s => s = rest ⦄ tail fuel acc ⦃ fun r s => r = acc ∧ s = rest ⦄ := by
  rw [tail]; vcgen (errorOnMissingSpec := false) <;> grind

abbrev ItemSpec (b : Nat) : Prop :=
  ∀ rest fuel, ⦃ fun s => s = enc b ++ rest ⦄ item fuel ⦃ fun r s => r = b ∧ s = rest ⦄

theorem viaBinder (b : Nat) (rest : List Char) (f : Nat)
    (hItem : ⦃ fun s => s = enc b ++ rest ⦄ item f ⦃ fun r s => r = b ∧ s = rest ⦄)
    (hstop : ∀ acc, ⦃ fun s => s = rest ⦄ tail f acc ⦃ fun r s => r = acc ∧ s = rest ⦄) :
    ∀ acc, ⦃ fun s => s = '+' :: (enc b ++ rest) ⦄ tail (f + 1) acc
      ⦃ fun r s => r = acc + b ∧ s = rest ⦄ := by
  intro acc; rw [tail]
  vcgen [hItem, hstop] <;> grind

theorem viaHave (b : Nat) (rest : List Char) (f : Nat)
    (H : ItemSpec b) (hplus : ¬ rest.head? = some '+') :
    ∀ acc, ⦃ fun s => s = '+' :: (enc b ++ rest) ⦄ tail (f + 1) acc
      ⦃ fun r s => r = acc + b ∧ s = rest ⦄ := by
  intro acc
  have hItem := H rest f
  have hstop := fun acc => tail_stop rest f acc hplus
  rw [tail]
  vcgen [hItem, hstop] <;> grind

-- `*` pulls the quantified `H` into the spec set, but the named `hItem` still outranks it.
theorem viaStar (b : Nat) (rest : List Char) (f : Nat)
    (H : ItemSpec b) (hplus : ¬ rest.head? = some '+') :
    ∀ acc, ⦃ fun s => s = '+' :: (enc b ++ rest) ⦄ tail (f + 1) acc
      ⦃ fun r s => r = acc + b ∧ s = rest ⦄ := by
  intro acc
  have hItem := H rest f
  have hstop := fun acc => tail_stop rest f acc hplus
  rw [tail]
  vcgen [hItem, hstop, *] <;> grind

-- `leaf` is opaque so `vcgen` must consult a spec rather than compute the program.
opaque leaf : StateM Nat Nat

@[spec] axiom leaf_default : ⦃ fun _ => True ⦄ leaf ⦃ fun _ _ => True ⦄

-- A named local spec is chosen over a registered `@[spec]` that also matches `leaf`.
theorem namedBeatsSpec (hNamed : ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄) :
    ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄ := by
  vcgen [hNamed] <;> grind

@[spec high] axiom leaf_high : ⦃ fun _ => True ⦄ leaf ⦃ fun _ _ => True ⦄

-- A `high` annotation, which outranks default specs, does not shadow a named local: the named
-- local is still chosen.
theorem specHighLoses (hNamed : ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄) :
    ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄ := by
  vcgen [hNamed] <;> grind

-- A spec supplied as a term rather than a bare identifier still enters the call-site band, so it
-- outranks the `@[spec high]`.
theorem termBeatsSpecHigh (hNamed : ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄) :
    ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄ := by
  vcgen [show ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄ from hNamed] <;> grind

@[spec high + 30] axiom leaf_above : ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄

-- A priority above the call-site band still overrides a named local.
theorem specHighestWins (hNamed : ⦃ fun _ => True ⦄ leaf ⦃ fun _ _ => True ⦄) :
    ⦃ fun _ => True ⦄ leaf ⦃ fun r _ => r = 7 ⦄ := by
  vcgen [hNamed] <;> grind

@[irreducible] def bumpSnd {σ : Type} : StateM (σ × Nat) Nat := do
  let n ← Prod.snd <$> get
  modify (fun s => (s.1, s.2 + 1))
  pure n

@[spec] theorem bumpSnd_lossy {σ : Type} (o : Nat) :
    ⦃ fun s => s.2 = o ⦄ (bumpSnd : StateM (σ × Nat) Nat) ⦃ fun r s => r = o ∧ s.2 = o + 1 ⦄ := by
  unfold bumpSnd; vcgen <;> grind

-- A bracketed definition is unfolded ahead of the lossy `@[spec]` on the same program, recovering
-- `s.1`, which the spec drops. The variable state `σ × Nat` keys the unfolding and the spec alike.
theorem unfoldBeatsSpec {σ : Type} (a : σ) :
    ⦃ fun s => s.1 = a ⦄ (bumpSnd : StateM (σ × Nat) Nat) ⦃ fun _ s => s.1 = a ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen [bumpSnd] <;> grind
