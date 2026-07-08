import Lean
import Std.Tactic.BVDecide.Bitblast.BVExpr

open Lean
open Std.Tactic.BVDecide

def groupAssignmentsBySymVars (assignments : List (Std.HashMap Nat BVExpr.PackedBitVec))
    : Std.HashMap (BVExpr w) (List BVExpr.PackedBitVec) := Id.run do
  let mut res : Std.HashMap (BVExpr w) (List BVExpr.PackedBitVec) := Std.HashMap.emptyWithCapacity
  let ex := assignments[0]!
  for (const, _) in ex.toArray do
    let constVar : BVExpr w := BVExpr.var const
    let _ := res.getD constVar []
  res

