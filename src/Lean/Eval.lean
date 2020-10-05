/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Environment

namespace Lean

universe u

/-- `HasEval` extension that gives access to the current environment & options.
    The basic `HasEval` class is in the prelude and should not depend on these
    types. -/
class MetaHasEval (α : Type u) :=
(eval : Environment → Options → α → forall (hideUnit : optParam Bool true), IO Environment)

instance metaHasEvalOfHasEval {α : Type u} [HasEval α] : MetaHasEval α :=
⟨fun env opts a hideUnit => do HasEval.eval (fun _ => a) hideUnit; pure env⟩

def runMetaEval {α : Type u} [MetaHasEval α] (env : Environment) (opts : Options) (a : α) : IO (String × Except IO.Error Environment) :=
IO.FS.withIsolatedStreams (MetaHasEval.eval env opts a false)

end Lean
