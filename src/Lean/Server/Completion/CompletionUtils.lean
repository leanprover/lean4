/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Marc Huisinga
-/
prelude
import Init.Prelude
import Lean.Elab.InfoTree.Types

namespace Lean.Server.Completion
open Elab

inductive HoverInfo : Type where
  | after
  | inside (delta : Nat)

structure ContextualizedCompletionInfo where
  hoverInfo : HoverInfo
  ctx       : ContextInfo
  info      : CompletionInfo

end Lean.Server.Completion
