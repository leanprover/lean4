/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Init.Grind.Interactive
namespace Lean.Elab.Tactic.Grind

@[builtin_grind_tactic Lean.Parser.Tactic.Grind.«done»] def evalDone : GrindTactic := fun _ =>
  done

end Lean.Elab.Tactic.Grind
