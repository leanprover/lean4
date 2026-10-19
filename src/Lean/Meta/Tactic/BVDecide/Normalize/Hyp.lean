/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Message

public section

/-!
This module defines the hypotheses that the `bv_normalize` preprocessing pipeline operates on.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

inductive HypSource where
  | lctx (fvar : FVarId)
  | enumDomain (n : Name)
  | structureProjection (e : Expr)
  | andFlattened (s : HypSource)
  | grind
  | cegar
  | epr
  deriving Inhabited, Hashable, BEq

partial instance : ToMessageData HypSource where
  toMessageData s :=
    go s
where
  go (s : HypSource) : MessageData :=
    match s with
    | .lctx fvar => m!"assumption {mkFVar fvar}"
    | .enumDomain n => m!"enum domain size lemma for {n}"
    | .structureProjection e => m!"structure lemma projection: {e}"
    | .andFlattened s => m!"and flattening from {go (stripFlatten s)}"
    | .grind => m!"grind state"
    | .cegar => m!"cegar refinement loop"
    | .epr => m!"EPR encoding"

  stripFlatten (s : HypSource) : HypSource :=
    match s with
    | .andFlattened s => stripFlatten s
    | _ => s

structure Hyp where
  name : Name
  type : Expr
  value : Expr
  source : HypSource
  deriving Inhabited

instance : BEq Hyp where
  beq lhs rhs := lhs.type == rhs.type

instance : Hashable Hyp where
  hash hyp := hash hyp.type

instance : ToMessageData Hyp where
  toMessageData hyp := toMessageData hyp.type

end Normalize
end Lean.Meta.Tactic.BVDecide
