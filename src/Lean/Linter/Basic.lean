/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

prelude
public import Lean.Linter.Init
public import Lean.Elab.Command

/-! # Basic linting functionality

This file publicly imports the basic functionality necessary for linting, namely
1. The linter option API (`Lean.Linter.Init`)
2. The `CommandElabM` API (`Lean.Elab.Command`)
-/

public section

namespace Lean

open Elab Command

/--
Given a command elaborator `cmd`, returns a new command elaborator that
first peels off and evaluates `set_option ... in ...` syntax recursively, updating the options
accordingly, and then invokes `cmd` on the inner syntax.

This is expected to be used in linters, after elaboration is complete. It is not appropriate for
ordinary elaboration of outer `set_option`s, since it
* does not update the infotrees with info for the `set_option` commands
* silently ignores failures in setting the given options (e.g. we do not error if the option is
  unknown or the wrong type of value is provided), as these should have been reported during
  original elaboration.
-/
partial def withSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in &&
     stx[0].getKind == ``Lean.Parser.Command.set_option then
      -- Do not modify the infotrees when elaborating, and silently ignore errors.
      let opts ← withEnableInfoTree false try
          (·.1) <$> elabSetOption stx[0][1] stx[0][3]
        catch _ => getOptions
      withScope ({ · with opts }) do withSetOptionIn cmd stx[2]
  else
    cmd stx

end Lean
