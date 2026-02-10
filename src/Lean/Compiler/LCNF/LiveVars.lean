/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.DependsOn

/-!
This file implements an auxiliary algorithm to determine whether a variable is live
(that is, might be used during execution) in a piece of impure LCNF code. This information is
relevant to determine potential reset-reuse pairs. Note that this algorithm assumes the piece of
code it is operating on has already been internalized.

The key difference of this algorithm compared to `dependsOn` is that it also considers non-syntactic
uses.

For example, given a piece of code `B`:
```
let x : = ...;
jmp jp1 x
```
where `jp1` is defined to be:
```
jp jp1 x :=
  let res := f x y
  return res;
```
this algorithm will identify `y` as being live in `B` because it is used through the jump to `jp1`.
-/

namespace Lean.Compiler.LCNF

structure Context where
  /--
  A cache for an `FVarIdSet` consisting of just `targetId`.
  -/
  targetSet : FVarIdSet
  /--
  The variable we are trying to determine for whether it is live.
  -/
  targetId : FVarId

structure State where
  /--
  The set of visited join points so we do not re-visit the same join point from multiple jumps.
  -/
  visitedJps : FVarIdHashSet := {}

abbrev LiveM := ReaderT Context <| StateT State CompilerM

/--
Determine whether `fvarId` is live in `c`. Assumes that `c` and all of its transitively reachable
join-points are internalized.
-/
public partial def Code.isFVarLiveIn (c : Code .impure) (fvarId : FVarId) : CompilerM Bool := do
  go c |>.run { targetSet := { fvarId }, targetId := fvarId } |>.run' {}
where
  go (c : Code .impure) : LiveM Bool := do
    match c with
    | .let decl k => (pure <| decl.dependsOn (← read).targetSet) <||> go k
    | .jp decl k => go decl.value <||> (do markJpVisited decl.fvarId; go k)
    | .uset var _ y k _ | .sset var _ _ y _ k _ =>
      visitVar var <||> visitVar y <||> go k
    | .cases c => visitVar c.discr <||> c.alts.anyM (go ·.getCode)
    | .jmp fvarId args =>
      (pure <| args.any (·.dependsOn (← read).targetSet)) <||> do
        if (← get).visitedJps.contains fvarId then
          return false
        else
          let some decl ← findFunDecl? fvarId | unreachable!
          markJpVisited fvarId
          go decl.value
    | .return var => visitVar var
    | .unreach .. => return false

  @[inline]
  visitVar (x : FVarId) : LiveM Bool :=
    return x == fvarId

  @[inline]
  markJpVisited (jp : FVarId) : LiveM Unit := do
    modify fun s => { s with visitedJps := s.visitedJps.insert jp }

end Lean.Compiler.LCNF
