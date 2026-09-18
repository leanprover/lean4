/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Bootstrap

namespace Lean.Cadical.Internal

@[extern "lean_cadical_signature"]
opaque getSignature (u : Unit) : String

public def signature : String := getSignature ()

end Lean.Cadical.Internal
