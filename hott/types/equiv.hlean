/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.equiv
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about the types equiv and is_equiv
-/

--import types.sigma

open eq is_trunc

namespace is_equiv
  open equiv
  context
    parameters {A B : Type} (f : A → B) [H : is_equiv f]
    include H


  end
  variables {A B : Type} (f : A → B)

  theorem is_hprop_is_equiv [instance] : is_hprop (is_equiv f) :=
  sorry

end is_equiv

namespace equiv
  open is_equiv
  variables {A B : Type}

  protected definition eq_mk' {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apD011 equiv.mk p !is_hprop.elim

  protected definition eq_mk {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by (cases f; cases f'; apply (equiv.eq_mk' p))
end equiv
