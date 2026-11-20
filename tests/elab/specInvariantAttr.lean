import Std.WP

set_option sym.debug true

/-!
Tests that `@[spec_invariant_type]` works end-to-end with `vcgen` and a custom invariant type: we
define a type, tag it, provide a spec using it, and check that `vcgen` classifies the invariant goal
as an invariant (so that the `invariants` syntax applies) rather than as a verification condition.
-/

open Std.WP Lean.Order

set_option experimental.vcgen true

@[spec_invariant_type]
def MyStringInvariant (s : String) (β : Type u) (Pred : Type uₚ) :=
  s.Pos → β → Pred

section
universe u₂ v uₚ uₑ
variable {β : Type u₂} {m : Type u₂ → Type v} {Pred : Type uₚ} {EPosts : Type uₑ}
variable [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]

-- The same as `Std.WP.Spec.forIn_string`, but with `MyStringInvariant` instead of
-- `StringInvariant`.
@[spec high]
axiom mySpec_forIn_string
    {s : String} {init : β} {f : Char → β → m (ForInStep β)}
    (inv : MyStringInvariant s β Pred)
    {eposts : EPosts}
    (step : ∀ pos b (h : pos ≠ s.endPos),
      Triple
        (f (pos.get h) b)
        (inv pos b)
        (fun r => match r with
          | .yield b' => inv (pos.next h) b'
          | .done b' => inv s.endPos b')
        eposts) :
    Triple (forIn s init f) (inv s.startPos init) (fun b => inv s.endPos b) eposts

end

def stringLoop (s : String) : Id Unit := do
  for _ in s do
    pure ()

theorem stringLoop_correct (s : String) :
    ⦃ True ⦄ stringLoop s ⦃ fun _ => True ⦄ := by
  vcgen [stringLoop] invariants
  · fun _ _ => True
  with finish
