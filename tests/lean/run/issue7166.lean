prelude
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Basic
import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Sat.AIG

namespace BVExpr
namespace bitblast

variable [Hashable α] [DecidableEq α]

namespace blastShiftLeftConst

-- set_option trace.Elab.definition.fixedParams true in
set_option debug.skipKernelTC true
-- set_option trace.Elab.definition.wf true in
set_option pp.proofs true
theorem go_denote_eq {w : Nat} (distance : Nat) (curr : Nat) (assign : α → Bool)
    (idx : Nat) (hidx1 : idx < w)
     (aig : AIG α)  (input : AIG.RefVec aig w)
    (s : AIG.RefVec aig curr)   (hcurr : curr ≤ w)
    :
        curr ≤ idx
          →
        ⟦
          (go aig input distance curr hcurr s).aig,
          (go aig input distance curr hcurr s).vec.get idx hidx1,
          assign
        ⟧
          =
        if hidx : idx < distance then
          false
        else
          ⟦aig, input.get (idx - distance) (by sorry), assign⟧
        := by
  intro hidx2
  generalize hgo : go aig input distance curr hcurr s = res
  unfold go at hgo
  split at hgo
  · cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq => sorry
    | inr =>
      split at hgo
      · split
        · next hidx =>
          rw [← hgo]
          dsimp
          rw [go_denote_eq]
          all_goals sorry
        · sorry
      · sorry
  · sorry
termination_by w - curr
decreasing_by sorry
