/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do

public section

namespace Lean.Elab.Do

open Lean Parser Meta Elab Do

@[builtin_do_elab Lean.Parser.Term.doReturn] def elabDoReturn : DoElab := fun stx cont => do
  let `(doElem| return $e) := stx | throwUnsupportedSyntax
  let returnCont ← getReturnCont
  let e ← elabTermEnsuringType e returnCont.resultType
  mapLetDeclZeta returnCont.resultName returnCont.resultType e fun _ =>
    returnCont.k
