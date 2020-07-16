/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.DeclModifiers

namespace Lean
namespace Elab
namespace Command
namespace Structure

inductive FieldKind
| newField | fromParent | subobject

structure FieldDecl :=
(fvar          : Expr)
(defaultVal?   : Option Expr)
(hasNewDefault : Bool) -- if true, (re-)declare default value in this structure
(kind          : FieldKind)
(inferMod      : Bool)

end Structure

def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

end Command
end Elab
end Lean
