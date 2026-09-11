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
# Compilable Acc.rec, Acc.rec' and WellFounded.fix

This module supplies `@[csimp]` lemmas so that `Acc.rec`, `Acc.rec'`, `WellFounded.fixF` and
`WellFounded.fix` compile to direct recursive code, even though their logical definitions are
noncomputable.

Without this, the following code would fail to compile, as `WellFounded.fix` is noncomputable.

```
def log2p1 : Nat → Nat :=
  WellFounded.fix Nat.lt_wfRel.2 fun n IH =>
    let m := n / 2
    if h : m < n then
      IH m h + 1
    else
      0
```
-/

namespace Acc

public instance wfRel {r : α → α → Prop} : WellFoundedRelation { val // Acc r val } where
  rel := InvImage r (·.1)
  wf  := ⟨fun ac => InvImage.accessible _ ac.2⟩

-- `@[csimp]` demands that both sides of a replacement theorem have identical universe parameter
-- lists, so the implementations below list the motive's universe first, as `Acc.rec` does.
/-- A compilable version of `Acc.rec` and `Acc.rec'`. -/
@[specialize, elab_as_elim] public def recC {motive : (a : α) → Acc r a → Sort v}
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (Acc.intro x h))
    {a : α} (t : Acc r a) : motive a t :=
  intro a (fun _ h => t.inv h) (fun _ hr => recC intro (t.inv hr))
termination_by Subtype.mk a t

@[csimp] public theorem rec_eq_recC : @Acc.rec = @Acc.recC := by
  funext α r motive intro a t
  induction t with
  | intro x h ih =>
    rw [recC]
    dsimp only
    congr; funext y hr; exact ih _ hr

@[csimp] public theorem rec'_eq_recC : @Acc.rec' = @Acc.recC := by
  funext α r motive intro a t
  induction t with
  | intro x h ih =>
    rw [recC, Acc.rec'_intro]
    congr; funext y hr; exact ih _ hr

/-- A compilable version of `Acc.recOn'`. -/
@[inline] public abbrev recOnC {motive : (a : α) → Acc r a → Sort v} {a : α} (t : Acc r a)
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (Acc.intro x h)) : motive a t :=
  t.recC intro

@[csimp] public theorem recOn'_eq_recOnC : @Acc.recOn' = @Acc.recOnC := by
  funext α r motive a t intro
  rw [Acc.recOn', rec'_eq_recC, Acc.recOnC]

/-- A compilable version of `Acc.ndrec` and `Acc.ndrec'`. -/
@[inline] public abbrev ndrecC {C : α → Sort v}
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    {a : α} (n : Acc r a) : C a :=
  n.recC m

@[csimp] public theorem ndrec_eq_ndrecC : @Acc.ndrec = @Acc.ndrecC := by
  funext α r motive intro a t
  rw [Acc.ndrec, rec_eq_recC, Acc.ndrecC]

@[csimp] public theorem ndrec'_eq_ndrecC : @Acc.ndrec' = @Acc.ndrecC := by
  funext α r motive intro a t
  rw [Acc.ndrec', rec'_eq_recC, Acc.ndrecC]

/-- A compilable version of `Acc.ndrecOn` and `Acc.ndrecOn'`. -/
@[inline] public abbrev ndrecOnC {C : α → Sort v} {a : α} (n : Acc r a)
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → r y x → C y) → C x) : C a :=
  n.recC m

@[csimp] public theorem ndrecOn_eq_ndrecOnC : @Acc.ndrecOn = @Acc.ndrecOnC := by
  funext α r motive intro a t
  rw [Acc.ndrecOn, rec_eq_recC, Acc.ndrecOnC]

@[csimp] public theorem ndrecOn'_eq_ndrecOnC : @Acc.ndrecOn' = @Acc.ndrecOnC := by
  funext α r motive intro a t
  rw [Acc.ndrecOn', rec'_eq_recC, Acc.ndrecOnC]

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
