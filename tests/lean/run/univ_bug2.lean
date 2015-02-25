----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic data.nat
open nat

-- first define a class of homogeneous equality
inductive simplifies_to [class] {T : Type} (t1 t2 : T) : Prop :=
mk : t1 = t2 → simplifies_to t1 t2

namespace simplifies_to

theorem get_eq {T : Type} {t1 t2 : T} (C : simplifies_to t1 t2) : t1 = t2 :=
simplifies_to.rec (λx, x) C

theorem infer_eq {T : Type} (t1 t2 : T) [C : simplifies_to t1 t2] : t1 = t2 :=
simplifies_to.rec (λx, x) C

theorem simp_app [instance] (S : Type) (T : Type) (f1 f2 : S → T) (s1 s2 : S)
   [C1 : simplifies_to f1 f2] [C2 : simplifies_to s1 s2] : simplifies_to (f1 s1) (f2 s2) :=
mk (congr (get_eq C1) (get_eq C2))

theorem test1 (S : Type) (T : Type) (f1 f2 : S → T) (s1 s2 : S) (Hf : f1 = f2) (Hs : s1 = s2) :
  f1 s1 = f2 s2 :=
have Rs [visible] : simplifies_to f1 f2, from mk Hf,
have Cs [visible] : simplifies_to s1 s2, from mk Hs,
infer_eq _ _

end simplifies_to
