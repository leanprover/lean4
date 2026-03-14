import Std.Tactic.Do
import Std
set_option backward.do.legacy false

open Std Do

set_option grind.warning false
set_option mvcgen.warning false

-- Test that `@[mvcgen_invariant_type]` works end-to-end with a custom invariant type.
-- We replicate the `StringInvariant` setup locally: define a type, tag it, provide a spec,
-- and verify that `mvcgen` classifies the invariant goal as `inv1` rather than `vc1`.

@[mvcgen_invariant_type]
abbrev MyStringInvariant (s : String) (β : Type u) (ps : PostShape.{u}) :=
  PostCond (s.Pos × β) ps

section
universe u₁ u₂ v
variable {β : Type (max u₁ u₂)} {m : Type (max u₁ u₂) → Type v} {ps : PostShape.{max u₁ u₂}}
variable [Monad m] [WPMonad m ps]

-- This is the same as `Spec.forIn_string` from `Std.Do.Triple.SpecLemmas`, but with
-- `MyStringInvariant` instead of `PostCond` so that `mvcgen` classifies the goal as an invariant.
@[spec high]
axiom mySpec_forIn_string
    {s : String} {init : β} {f : Char → β → m (ForInStep β)}
    (inv : MyStringInvariant s β ps)
    (step : ∀ pos b (h : pos ≠ s.endPos),
      Triple
        (f (pos.get h) b)
        (inv.1 (pos, b))
        (fun r => match r with
          | .yield b' => inv.1 (pos.next h, b')
          | .done b' => inv.1 (s.endPos, b'), inv.2)) :
    Triple (forIn s init f) (inv.1 (s.startPos, init)) (fun b => inv.1 (s.endPos, b), inv.2)

end

def stringLoop (s : String) : Id Unit := do
  for _ in s do
    pure ()

theorem stringLoop_correct (s : String) :
    ⦃⌜True⌝⦄ stringLoop s ⦃⇓ _ => ⌜True⌝⦄ := by
  -- With `@[mvcgen_invariant_type]` on `MyStringInvariant`, mvcgen classifies the
  -- loop invariant goal as `inv1` rather than `vc1`, enabling the `invariants` syntax.
  mvcgen [stringLoop] invariants
  · ⇓ _ => ⌜True⌝
  with grind
