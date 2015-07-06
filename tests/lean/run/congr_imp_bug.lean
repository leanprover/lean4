----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------
open function

namespace congr

inductive struc [class] {T1 : Type} {T2 : Type} (R1 : T1 → T1 → Prop) (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
mk : (∀x y : T1, R1 x y → R2 (f x) (f y)) → struc R1 R2 f

definition app {T1 : Type} {T2 : Type} {R1 : T1 → T1 → Prop} {R2 : T2 → T2 → Prop}
    {f : T1 → T2} (C : struc R1 R2 f) {x y : T1} : R1 x y → R2 (f x) (f y) :=
struc.rec id C x y

inductive struc2 {T1 : Type} {T2 : Type} {T3 : Type} (R1 : T1 → T1 → Prop)
    (R2 : T2 → T2 → Prop) (R3 : T3 → T3 → Prop) (f : T1 → T2 → T3) : Prop :=
mk2 : (∀(x1 y1 : T1) (x2 y2 : T2), R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2)) →
    struc2 R1 R2 R3 f

definition app2 {T1 : Type} {T2 : Type} {T3 : Type} {R1 : T1 → T1 → Prop}
    {R2 : T2 → T2 → Prop} {R3 : T3 → T3 → Prop} {f : T1 → T2 → T3}
    (C : struc2 R1 R2 R3 f) {x1 y1 : T1} {x2 y2 : T2}
  : R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
struc2.rec id C x1 y1 x2 y2

theorem compose21
    {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {T4 : Type} {R4 : T4 → T4 → Prop}
    {g : T2 → T3 → T4} (C3 : congr.struc2 R2 R3 R4 g)
    ⦃T1 : Type⦄  -- nice!
    {R1 : T1 → T1 → Prop}
    {f1 : T1 → T2} (C1 : congr.struc R1 R2 f1)
    {f2 : T1 → T3} (C2 : congr.struc R1 R3 f2) :
  congr.struc R1 R4 (λx, g (f1 x) (f2 x)) := struc.mk (take x1 x2 H, app2 C3 (app C1 H) (app C2 H))

theorem congr_and : congr.struc2 iff iff iff and := sorry

theorem congr_and_comp [instance] {T : Type} {R : T → T → Prop} {f1 f2 : T → Prop}
     (C1 : struc R iff f1) (C2 : struc R iff f2) :
   congr.struc R iff (λx, f1 x ∧ f2 x) := congr.compose21 congr_and C1 C2

end congr
