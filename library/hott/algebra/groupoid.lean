-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import .precategory.basic .precategory.morphism

open path function prod sigma truncation morphism nat precategory

structure foo (A : Type) := (bsp : A)

structure groupoid [class] (ob : Type) extends precategory ob :=
  (all_iso : Π ⦃a b : ob⦄ (f : hom a b),
    @is_iso ob (precategory.mk hom _ _ _ assoc id_left id_right) a b f)

namespace groupoid

set_option pp.universes true
universe variable l
definition path_precategory (A : Type.{l})
    (H : is_trunc 1 A) : precategory.{l l} A :=
begin
  fapply precategory.mk,
    intros (a, b), exact (a ≈ b),
    intros, apply succ_is_trunc, exact H,
    intros (a, b, c, p, q), exact (@concat A a b c q p),
    intro a, apply idp,
    intros, apply concat_pp_p,
    intros, apply concat_p1,
    intros, apply concat_1p,
end

end groupoid
