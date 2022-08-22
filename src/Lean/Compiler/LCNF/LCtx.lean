/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.LocalContext

namespace Lean.Compiler.LCNF

/--
LCNF local context.
-/
abbrev LCtx := Std.HashMap FVarId LocalDecl

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) : LocalContext :=
  lctx.fold (init := {}) fun lctx _ localDecl => lctx.addDecl localDecl

end Lean.Compiler.LCNF