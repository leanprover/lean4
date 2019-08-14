/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.elaborator.alias
import init.lean.elaborator.basic

namespace Lean
namespace Elab

def elabTerm (stx : Syntax Expr) (expectedType : Option Expr) : Elab (Syntax Expr) :=
stx.ifNode
  (fun n => do
    s ← get;
    let tables := termElabAttribute.ext.getState s.env;
    let k      := n.getKind;
    match tables.find k with
    | some elab => elab n expectedType
    | none      => logErrorAndThrow stx ("term elaborator failed, no support for syntax '" ++ toString k ++ "'"))
  (fun _=>
    match stx with
    | Syntax.other e => pure stx
    | _              => throw "term elaborator failed, unexpected syntax")

end Elab
end Lean
