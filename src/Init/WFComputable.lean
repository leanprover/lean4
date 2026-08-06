/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
prelude
public import Init.WF
import Init.NotationExtra
import Init.WFTactics

/-!
# Compilable WellFounded.fix

This module supplies `@[csimp]` lemmas so that `WellFounded.fixF` and
`WellFounded.fix` compile to direct recursive code, even though their
logical definitions go through `Classical.choice`.

Under the no-large-elim-of-Acc experiment, `Acc.rec` is restricted to
`Prop` motives, so the original `Acc.recC` / `Acc.ndrec` csimp pairs no
longer typecheck (the recursor has lost its motive universe parameter).
Code that compiled because of those rules now needs to rely on these
`WellFounded.*` csimp rules instead.
-/

namespace Acc

public instance wfRel {r : α → α → Prop} : WellFoundedRelation { val // Acc r val } where
  rel := InvImage r (·.1)
  wf  := ⟨fun ac => InvImage.accessible _ ac.2⟩

end Acc

namespace WellFounded

/-- A compilable version of `WellFounded.fixF`. -/
@[specialize] public def fixFC {α : Sort u} {r : α → α → Prop}
    {C : α → Sort v} (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) (a : Acc r x) : C x :=
  F x (fun y h => fixFC F y (a.inv h))
termination_by Subtype.mk x a

unseal fixFC

private theorem fixFC_graph {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) (a : Acc r x) :
    FixGraph F x (fixFC F x a) := by
  induction a with
  | intro x _ ih =>
    rw [fixFC]
    exact FixGraph.mk x _ (fun y h => ih y h)

@[csimp] public theorem fixF_eq_fixFC : @fixF = @fixFC := by
  funext α r C F x a
  exact FixGraph_funct F a _ _ (fixFImpl_graph F x a) (fixFC_graph F x a)

/-- A compilable version of `WellFounded.fix`. -/
@[specialize] public def fixC {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x (fun y _ => fixC hwf F y)
termination_by hwf.wrap x

unseal fixC

private theorem fixC_graph {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)
    (x : α) (acx : Acc r x) : FixGraph F x (fixC hwf F x) := by
  induction acx with
  | intro x _ ih =>
    rw [fixC]
    exact FixGraph.mk x _ (fun y h => ih y h)

@[csimp] public theorem fix_eq_fixC : @fix = @fixC := by
  funext α C r hwf F x
  exact FixGraph_funct F (apply hwf x) _ _
    (fixFImpl_graph F x (apply hwf x))
    (fixC_graph hwf F x (apply hwf x))

end WellFounded
