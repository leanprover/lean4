/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.Reader
import Init.System.IO
import Init.Lean.Environment

namespace Lean

universe u

/-- `HasEval` extension that gives access to the current environment & options.
    The basic `HasEval` class is in the prelude and should not depend on these
    types. -/
class MetaHasEval (α : Type u) :=
(eval : Environment → Options → α → forall (hideUnit : optParam Bool true), IO Unit)

instance metaHasEvalOfHasEval {α : Type u} [HasEval α] : MetaHasEval α :=
⟨fun env opts a hideUnit => HasEval.eval a hideUnit⟩

abbrev MetaIO := ReaderT (Environment × Options) IO

def MetaIO.getEnv : MetaIO Environment := do
ctx ← read; pure ctx.1

def MetaIO.getOptions : MetaIO Options := do
ctx ← read; pure ctx.2

instance MetaIO.metaHasEval {α} [MetaHasEval α] : MetaHasEval (MetaIO α) :=
⟨fun env opts x _ => x (env, opts) >>= MetaHasEval.eval env opts⟩

instance MetaIO.monadIO : MonadIO MetaIO :=
⟨fun _ x _ => x⟩

end Lean
