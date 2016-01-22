/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Pointed Pushouts
-/
import .pushout types.pointed

open eq pushout

namespace pointed
  
  definition pointed_pushout [instance] [constructor] {TL BL TR : Type} [HTL : pointed TL]
    [HBL : pointed BL] [HTR : pointed TR] (f : TL → BL) (g : TL → TR) : pointed (pushout f g) :=
  pointed.mk (inl (point _))

end pointed

open pointed

namespace pushout
  section
  parameters {TL BL TR : Type*} (f : TL →* BL) (g : TL →* TR)

  definition Pushout [constructor] : Type* :=
  pointed.mk' (pushout f g)
  
  parameters {f g}
  definition pinl [constructor] : BL →* Pushout :=
  pmap.mk inl idp

  definition pinr [constructor] : TR →* Pushout :=
  pmap.mk inr ((ap inr (respect_pt g))⁻¹ ⬝ !glue⁻¹ ⬝ (ap inl (respect_pt f)))

  definition pglue (x : TL) : pinl (f x) = pinr (g x) := -- TODO do we need this?
  !glue

  definition prec {P : Pushout → Type} (Pinl : Π x, P (pinl x)) (Pinr : Π x, P (pinr x))
    (H : Π x, Pinl (f x) =[pglue x] Pinr (g x)) : (Π y, P y) :=
  pushout.rec Pinl Pinr H

  end
end pushout
