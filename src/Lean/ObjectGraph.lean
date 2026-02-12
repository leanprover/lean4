/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Prelude
public import Init.Data.String.Bootstrap

namespace Lean

@[extern "lean_object_graph_to_dot"]
public opaque objectGraphToDot : @& α → String

end Lean
