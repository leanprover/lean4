-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.path hott.trunc data.sigma data.prod

open path prod

inductive is_pointed [class] (A : Type) :=
  pointed_mk : Π(a : A), is_pointed A

namespace is_pointed
  variables {A B : Type} (f : A → B)

  definition point (A : Type) [H : is_pointed A] : A :=
    is_pointed.rec (λinv, inv) H

  -- Any contractible type is pointed
  protected definition contr [instance] (H : Contr A) : is_pointed A :=
    pointed_mk (center H)

  -- A pi type with a pointed target is pointed
  protected definition pi [instance] {P : A → Type} [H : Πx, is_pointed (P x)]
      : is_pointed (Πx, P x) :=
    pointed_mk (λx, point (P x))

  -- A sigma type of pointed components is pointed
  protected definition sigma [instance] {P : A → Type} [G : is_pointed A]
      [H : is_pointed (P (point A))] : is_pointed (Σx, P x) :=
    pointed_mk (sigma.dpair (point A) (point (P (point A))))

  protected definition prod [H1 : is_pointed A] [H2 : is_pointed B]
      : is_pointed (A × B) :=
    pointed_mk (prod.mk (point A) (point B))

  protected definition loop_space (a : A) : is_pointed (a ≈ a) :=
    pointed_mk idp

end is_pointed
