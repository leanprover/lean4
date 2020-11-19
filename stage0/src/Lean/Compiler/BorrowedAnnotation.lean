/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
namespace Lean

def markBorrowed (e : Expr) : Expr :=
  mkAnnotation `borrowed e

@[export lean_is_marked_borrowed]
def isMarkedBorrowed (e : Expr) : Bool :=
  annotation? `borrowed e |>.isSome

end Lean
