/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import types.pointed .trunc_group

open nat eq pointed trunc is_trunc algebra

namespace eq

  definition homotopy_group [reducible] (n : ℕ) (A : Pointed) : Type :=
  trunc 0 (Ω[n] A)

  notation `π[`:95 n:0 `] `:0 A:95 := homotopy_group n A

  definition pointed_homotopy_group [instance] [constructor] (n : ℕ) (A : Pointed)
    : pointed (π[n] A) :=
  pointed.mk (tr rfln)

  definition group_homotopy_group [instance] [constructor] (n : ℕ) (A : Pointed)
    : group (π[succ n] A) :=
  trunc_group concat inverse idp con.assoc idp_con con_idp con.left_inv

  definition comm_group_homotopy_group [constructor] (n : ℕ) (A : Pointed)
    : comm_group (π[succ (succ n)] A) :=
  trunc_comm_group concat inverse idp con.assoc idp_con con_idp con.left_inv eckmann_hilton

  local attribute comm_group_homotopy_group [instance]

  definition Pointed_homotopy_group [constructor] (n : ℕ) (A : Pointed) : Pointed :=
  Pointed.mk (π[n] A)

  definition Group_homotopy_group [constructor] (n : ℕ) (A : Pointed) : Group :=
  Group.mk (π[succ n] A) _

  definition CommGroup_homotopy_group [constructor] (n : ℕ) (A : Pointed) : CommGroup :=
  CommGroup.mk (π[succ (succ n)] A) _

  definition fundamental_group [constructor] (A : Pointed) : Group :=
  Group_homotopy_group zero A

  notation `πP[`:95  n:0    `] `:0 A:95 := Pointed_homotopy_group n A
  notation `πG[`:95  n:0 ` +1] `:0 A:95 := Group_homotopy_group n A
  notation `πaG[`:95 n:0 ` +2] `:0 A:95 := CommGroup_homotopy_group n A

  prefix `π₁`:95 := fundamental_group


end eq
