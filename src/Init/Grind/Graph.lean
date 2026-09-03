/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Init.Tactics

/-!
TODO
-/

namespace Lean.Grind
open Parser Tactic Grind

/--
TODO
-/
syntax (name := grindGraph) "#grind_graph" (ppSpace configItem)* (ppSpace &"module")? ident+ (ppSpace "with" ppSpace str)? (ppSpace ">" ppSpace str)? : command

end Lean.Grind
