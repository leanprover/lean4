/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Elab.Command

namespace Lean

open Elab.Command Elab.Term

/--
`Eval` extension that gives access to the current environment & options.
The basic `Eval` class is in the prelude and should not depend on these
types.
-/
class MetaEval (α : Type u) where
  eval : α → (hideUnit : Bool) → CommandElabM (Option MessageData)

instance [Eval α] : MetaEval α where
  eval a hideUnit := return ← Eval.eval (hideUnit := hideUnit) fun _ => a

instance [ToMessageData α] : MetaEval α where
  eval a _ := return toMessageData a

instance : MetaEval Unit where
  eval _ hideUnit := return if hideUnit then none else some "()"

instance [MetaEval α] : MetaEval (BaseIO α) where
  eval a _ := do MetaEval.eval (hideUnit := true) (← liftIO a)

instance [MetaEval α] : MetaEval (IO α) where
  eval a _ := do MetaEval.eval (hideUnit := true) (← liftIO a)

instance [MetaEval α] : MetaEval (CoreM α) where
  eval a _ := do MetaEval.eval (hideUnit := true) (← liftCoreM a)

instance [MetaEval α] : MetaEval (MetaM α) where
  eval x _ := do MetaEval.eval (hideUnit := true) (← liftTermElabM x)

instance [MetaEval α] : MetaEval (TermElabM α) where
  eval x _ := do MetaEval.eval (hideUnit := true) (← liftTermElabM x)

instance [MetaEval α] : MetaEval (CommandElabM α) where
  eval x _ := do MetaEval.eval (hideUnit := true) (← x)

namespace EvalInstances

scoped instance (priority := low - 10) [Repr α] : ToMessageData α where
  toMessageData a := repr a

-- Otherwise we go via the blanket Format→MessageData instance.
scoped instance [ToMessageData ε] [ToMessageData α] : ToMessageData (Except ε α) where
  toMessageData
    | .error e => m!"Except.error ({e})"
    | .ok a => m!"Except.ok ({a})"

-- HACK: print strings with double quotes in `#eval`.
scoped instance (priority := high) : ToMessageData String where
  toMessageData s := repr s

end EvalInstances

end Lean
