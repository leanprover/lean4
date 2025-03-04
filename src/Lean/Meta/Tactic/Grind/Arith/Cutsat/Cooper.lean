/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat

def CooperSplit.numCases (s : CooperSplit) : Nat :=
  let a  := s.c₁.p.leadCoeff
  let b  := s.c₂.p.leadCoeff
  match s.c₃? with
  | none => if s.left then a.natAbs else b.natAbs
  | some c₃ =>
    let c  := c₃.p.leadCoeff
    let d  := c₃.d
    if s.left then
      Int.lcm a (a * d / Int.gcd (a * d) c)
    else
      Int.lcm b (b * d / Int.gcd (b * d) c)

end Lean.Meta.Grind.Arith.Cutsat
