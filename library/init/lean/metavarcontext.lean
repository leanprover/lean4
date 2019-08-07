/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.localcontext

namespace Lean

structure MetavarDecl :=
(userName : Name)
(lctx     : LocalContext)
(type     : Expr)

/-
A delayed assignment for a metavariable `?m`. It represents an assignment of the form
`?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
Note that `fvars` may not be defined in the local context for `?m`.
-/
structure DelayedMetavarAssignment :=
(lctx     : LocalContext)
(fvars    : List Expr)
(val      : Expr)

structure MetavarContext :=
(decls       : PersistentHashMap Name MetavarDecl := {})
(lAssignment : PersistentHashMap Name Level := {})
(eAssignment : PersistentHashMap Name Expr := {})
(dAssignment : PersistentHashMap Name DelayedMetavarAssignment := {})

namespace MetavarContext

end MetavarContext
end Lean
