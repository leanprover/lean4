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
@[inline]
def mkNotCached (aig : AIG α) (gate : Ref aig) : Entrypoint α :=
  ⟨aig, gate.not⟩

/--
Create an and gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
@[inline]
def mkAndCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  aig.mkAndGateCached input

/--
Create an or gate in the input AIG. This uses the builtin cache to enable automated subterm sharing.
-/
def mkOrCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- x or y = invert (invert x && invert y)
  let res := aig.mkAndGateCached <| input.invert true true
  let aig := res.aig
  let auxRef := res.ref
  ⟨aig, auxRef.not⟩

/--
Create an xor gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkXorCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  aig.mkXorGateCached input

/--
Create an equality gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkBEqCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a == b = !(a ^^ b)
  let neq := aig.mkXorGateCached input
  let aig := neq.aig
  let ref := neq.ref
  ⟨aig, ref.not⟩

/--
Create an implication gate in the input AIG. This uses the builtin cache to enable automated subterm
sharing.
-/
def mkImpCached (aig : AIG α) (input : BinaryInput aig) : Entrypoint α :=
  -- a -> b = (invert (a and (invert b)))
  let res := aig.mkAndGateCached <| input.invert false true
  let aig := res.aig
  let auxRef := res.ref
  ⟨aig, auxRef.not⟩

end AIG

end Sat
end Std
