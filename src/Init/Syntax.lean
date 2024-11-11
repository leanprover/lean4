/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/

prelude
import Init.Data.Array.Set

/-!
# Helper functions for `Syntax`.

These are delayed here to allow some time to bootstrap `Array`.
-/

namespace Lean.Syntax

/--
Updates the argument list without changing the node kind.
Does nothing for non-`node` nodes.
-/
def setArgs (stx : Syntax) (args : Array Syntax) : Syntax :=
  match stx with
  | node info k _ => node info k args
  | stx           => stx

/--
Updates the `i`'th argument of the syntax.
Does nothing for non-`node` nodes, or if `i` is out of bounds of the node list.
-/
def setArg (stx : Syntax) (i : Nat) (arg : Syntax) : Syntax :=
  match stx with
  | node info k args => node info k (args.setD i arg)
  | stx              => stx

end Lean.Syntax
