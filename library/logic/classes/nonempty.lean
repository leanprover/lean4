-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import .inhabited

using inhabited

namespace nonempty

inductive nonempty (A : Type) : Prop :=
nonempty_intro : A → nonempty A

definition nonempty_elim {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty_rec H2 H1

theorem inhabited_imp_nonempty [instance] {A : Type} (H : inhabited A) : nonempty A :=
nonempty_intro (default A)

end nonempty
