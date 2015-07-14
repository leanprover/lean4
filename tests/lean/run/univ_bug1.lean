----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic data.nat
open nat

namespace nsimp
-- set_option pp.universes true
-- set_option pp.implicit true

-- first define a class of homogeneous equality
inductive simplifies_to [class] {T : Type} (t1 t2 : T) : Prop :=
mk : t1 = t2 → simplifies_to t1 t2

theorem get_eq {T : Type} {t1 t2 : T} (C : simplifies_to t1 t2) : t1 = t2 :=
simplifies_to.rec (λx, x) C

theorem infer_eq {T : Type} (t1 t2 : T) {C : simplifies_to t1 t2} : t1 = t2 :=
simplifies_to.rec (λx, x) C

theorem simp_app [instance] (S T : Type) (f1 f2 : S → T) (s1 s2 : S)
   (C1 : simplifies_to f1 f2) (C2 : simplifies_to s1 s2) : simplifies_to (f1 s1) (f2 s2) :=
simplifies_to.mk (congr (get_eq C1) (get_eq C2))

end nsimp
