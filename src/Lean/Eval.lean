/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Environment

namespace Lean

universe u

/--
`Eval` extension that gives access to the current environment & options.
The basic `Eval` class is in the prelude and should not depend on these
types.
-/
class MetaEval (α : Type u) where
  eval : Environment → Options → α → (hideUnit : Bool) → IO Environment

instance {α : Type u} [Eval α] : MetaEval α :=
  ⟨fun env _ a hideUnit => do Eval.eval (fun _ => a) hideUnit; pure env⟩

def runMetaEval {α : Type u} [MetaEval α] (env : Environment) (opts : Options) (a : α) : IO (String × Except IO.Error Environment) :=
  IO.FS.withIsolatedStreams (MetaEval.eval env opts a false |>.toBaseIO)

end Lean
