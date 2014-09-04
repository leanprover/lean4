-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad
import .inhabited
open inhabited

inductive nonempty (A : Type) : Prop :=
intro : A → nonempty A

namespace nonempty
  definition elim [protected] {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
  rec H2 H1

  theorem inhabited_imp_nonempty [instance] {A : Type} (H : inhabited A) : nonempty A :=
  intro (default A)
end nonempty
