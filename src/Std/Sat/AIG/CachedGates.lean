/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.Cached
import Std.Sat.AIG.CachedLemmas

/-!
This module contains functions to construct basic logic gates while making use of the sub-circuit
cache if possible.
-/

namespace Std
namespace Sat

namespace AIG

variable {α : Type} [Hashable α] [DecidableEq α]

/--
Create a not gate in the input AIG. This uses the builtin cache to enable automated subterm sharing.
-/
def mkNotCached (aig : AIG α) (gate : Ref aig) : Entrypoint α :=
  -- ¬x = true && invert x
  let res := aig.mkConstCached true
  let aig := res.aig
  let constRef := res.ref
  aig.mkGateCached {
    lhs := {
      ref := constRef
      inv := false
    }
    rhs := {
      ref := gate.cast <| by
        intros
        apply LawfulOperator.le_size_of_le_aig_size (f := mkConstCached)
        omega
      inv := true
    }
  }

@[inline]
def BinaryInput.asGateInput {aig : AIG α} (input : BinaryInput aig) (linv rinv : Bool) :
    GateInput aig :=
  { lhs := { ref := input.lhs, inv := linv }, rhs := { ref := input.rhs, inv := rinv } }

/--
Create an and gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkAndCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  aig.mkGateCached <| input.asGateInput false false

/--
Create an or gate in the input AIG. This uses the builtin cache to enable automated subterm sharing.
-/
def mkOrCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x or y = true && (invert (invert x && invert y))
  let res := aig.mkGateCached <| input.asGateInput true true
  let aig := res.aig
  let auxRef := res.ref
  let res := aig.mkConstCached true
  let aig := res.aig
  let constRef := res.ref
  aig.mkGateCached {
      lhs := {
        ref := constRef
        inv := false
      },
      rhs := {
        ref := auxRef.cast <| by
          intros
          simp (config := { zetaDelta := true }) only
          apply LawfulOperator.le_size_of_le_aig_size (f := mkConstCached)
          omega
        inv := true
      }
    }

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkXorCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x xor y = (invert (invert (x && y))) && (invert ((invert x) && (invert y)))
  let res := aig.mkGateCached <| input.asGateInput false false
  let aig := res.aig
  let aux1Ref := res.ref
  let rinput :=
    (input.asGateInput true true).cast
      (by
        intros
        apply LawfulOperator.le_size_of_le_aig_size (f := mkGateCached)
        omega)
  let res := aig.mkGateCached rinput
  let aig := res.aig
  let aux2Ref := res.ref
  aig.mkGateCached {
    lhs := {
      ref := aux1Ref.cast <| by
        simp (config := { zetaDelta := true }) only
        apply LawfulOperator.le_size_of_le_aig_size (f := mkGateCached)
        omega
      inv := true
    },
    rhs := {
      ref := aux2Ref
      inv := true
    }
  }

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkBEqCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a == b = (invert (a && (invert b))) && (invert ((invert a) && b))
  let res := aig.mkGateCached <| input.asGateInput false true
  let aig := res.aig
  let aux1Ref := res.ref
  let rinput :=
    (input.asGateInput true false).cast
      (by
        intros
        apply LawfulOperator.le_size_of_le_aig_size (f := mkGateCached)
        omega)
  let res := aig.mkGateCached rinput
  let aig := res.aig
  let aux2Ref := res.ref
  aig.mkGateCached {
    lhs := {
      ref := aux1Ref.cast <| by
        simp (config := { zetaDelta := true }) only
        apply LawfulOperator.le_size_of_le_aig_size (f := mkGateCached)
        omega
      inv := true
    },
    rhs := {
      ref := aux2Ref
      inv := true
    }
  }

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkImpCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a -> b = true && (invert (a and (invert b)))
  let res := aig.mkGateCached <| input.asGateInput false true
  let aig := res.aig
  let auxRef := res.ref
  let res := aig.mkConstCached true
  let aig := res.aig
  let constRef := res.ref
  aig.mkGateCached {
    lhs := {
      ref := constRef
      inv := false
    },
    rhs := {
      ref := auxRef.cast <| by
        intros
        simp (config := { zetaDelta := true }) only
        apply LawfulOperator.le_size_of_le_aig_size (f := mkConstCached)
        omega
      inv := true
    }
  }

end AIG

end Sat
end Std
