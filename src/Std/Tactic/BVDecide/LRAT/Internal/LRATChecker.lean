/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Actions
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

inductive Result
  | success
  | outOfProof
  | rupFailure
deriving Inhabited, DecidableEq

instance : ToString Result where
  toString := fun
    | .success => "success"
    | .outOfProof => "out of proof"
    | .rupFailure => "rup failure"

open Formula

def lratChecker [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (prf : List (Action β α)) :
    Result :=
  match prf with
  | [] => .outOfProof
  | .addEmpty _ rupHints :: _ =>
    let (_, checkSuccess) := performRupAdd f Clause.empty rupHints
    if checkSuccess then
      .success
    else
      .rupFailure
  | .addRup _ c rupHints :: restPrf =>
    let (f, checkSuccess) := performRupAdd f c rupHints
    if checkSuccess then
      lratChecker f restPrf
    else
      .rupFailure
  | .addRat _ c pivot rupHints ratHints :: restPrf =>
    let (f, checkSuccess) := performRatAdd f c pivot rupHints ratHints
    if checkSuccess then
      lratChecker f restPrf
    else
      .rupFailure
  | .del ids :: restPrf => lratChecker (delete f ids) restPrf

end Internal
end LRAT
end Std.Tactic.BVDecide
