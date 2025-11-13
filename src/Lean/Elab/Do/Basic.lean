/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Term.TermElabM
public section

namespace Lean.Elab.Do

builtin_initialize registerTraceClass `Elab.do

-- @[builtin_term_elab «do»]
def elabDo : Term.TermElab := fun _e _expectedType? => do
  throwError "Not implemented yet"
