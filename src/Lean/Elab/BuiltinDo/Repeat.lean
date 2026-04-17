/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.BuiltinDo.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.For

public section

namespace Lean.Elab.Do

open Lean.Parser.Term

/--
Builtin do-element elaborator for `repeat` (syntax kind `Lean.doRepeat`).

Expands to `for _ in Loop.mk do ...`. A follow-up PR will drop the fallback macro
in `Init.While` (which currently preempts this elaborator) and extend this
elaborator to choose between `Loop.mk` and a well-founded `Repeat.mk` based on a
configuration option.
-/
@[builtin_doElem_elab Lean.doRepeat] def elabDoRepeat : DoElab := fun stx dec => do
  let `(doElem| repeat $seq) := stx | throwUnsupportedSyntax
  let expanded ← `(doElem| for _ in Loop.mk do $seq)
  Term.withMacroExpansion stx expanded <|
    withRef expanded <| elabDoElem ⟨expanded⟩ dec

end Lean.Elab.Do
