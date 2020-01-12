/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Data.Options

namespace Lean

def defaultMaxRecDepth := 512

def getMaxRecDepth (opts : Options) : Nat :=
opts.getNat `maxRecDepth defaultMaxRecDepth

@[init] def maxRecDepth : IO Unit :=
registerOption `maxRecDepth { defValue := defaultMaxRecDepth, group := "", descr := "maximum recursion depth for many Lean procedures" }

def maxRecDepthErrorMessage : String :=
"maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)"

end Lean
