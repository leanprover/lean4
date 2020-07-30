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
⟨fun env opts a hideUnit => do HasEval.eval a hideUnit; pure env⟩

abbrev MetaIO := ReaderT (Environment × Options) IO

def MetaIO.getEnv : MetaIO Environment := do
ctx ← read; pure ctx.1

def MetaIO.getOptions : MetaIO Options := do
ctx ← read; pure ctx.2

instance MetaIO.metaHasEval {α} [MetaHasEval α] : MetaHasEval (MetaIO α) :=
⟨fun env opts x _ => do
  a ← x (env, opts);
  MetaHasEval.eval env opts a⟩

instance MetaIO.monadIO : MonadIO MetaIO := {}

end Lean
