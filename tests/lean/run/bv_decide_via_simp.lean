import Std.Tactic.BVDecide
import Std.Tactic.RSimp
import Std.Tactic.RSimp.ConvTheorem

theorem ex (i : BitVec 5) : 2 * i &&& 1 = 0 := by bv_decide

/-- info: true -/
#guard_msgs in
#eval ex._reflection_def_1

def parsedProof : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  #[Std.Tactic.BVDecide.LRAT.Action.addRup 64 #[-183] #[1, 3],
    Std.Tactic.BVDecide.LRAT.Action.addRup 65 #[-8, -182] #[64, 7],
    Std.Tactic.BVDecide.LRAT.Action.addRup 66 #[8, 1] #[61],
    Std.Tactic.BVDecide.LRAT.Action.addRup 67 #[8] #[62, 66],
    Std.Tactic.BVDecide.LRAT.Action.addRup 68 #[-182] #[67, 65],
    Std.Tactic.BVDecide.LRAT.Action.addRup 69 #[-9] #[67, 57],
    Std.Tactic.BVDecide.LRAT.Action.addRup 70 #[-181] #[68, 67, 10],
    Std.Tactic.BVDecide.LRAT.Action.addRup 71 #[10] #[69, 62, 55],
    Std.Tactic.BVDecide.LRAT.Action.addRup 72 #[-180] #[70, 67, 13],
    Std.Tactic.BVDecide.LRAT.Action.addRup 73 #[-11] #[71, 51],
    Std.Tactic.BVDecide.LRAT.Action.addRup 74 #[-179] #[72, 67, 16],
    Std.Tactic.BVDecide.LRAT.Action.addRup 75 #[12] #[73, 62, 49],
    Std.Tactic.BVDecide.LRAT.Action.addRup 76 #[173] #[74, 62, 19],
    Std.Tactic.BVDecide.LRAT.Action.addRup 77 #[-13] #[75, 45],
    Std.Tactic.BVDecide.LRAT.Action.addRup 78 #[-140] #[76, 21],
    Std.Tactic.BVDecide.LRAT.Action.addRup 79 #[46] #[77, 62, 43],
    Std.Tactic.BVDecide.LRAT.Action.addRup 80 #[133] #[78, 62, 25],
    Std.Tactic.BVDecide.LRAT.Action.addRup 81 #[-47] #[79, 39],
    Std.Tactic.BVDecide.LRAT.Action.addRup 82 #[-99] #[80, 27],
    Std.Tactic.BVDecide.LRAT.Action.addRup 83 #[56] #[81, 62, 37],
    Std.Tactic.BVDecide.LRAT.Action.addRup 84 #[91] #[82, 62, 31],
    Std.Tactic.BVDecide.LRAT.Action.addEmpty 85 #[84, 83, 33]]

@[simp] theorem parse_aux :
  Std.Tactic.BVDecide.LRAT.parseLRATProof ex._cert_def_1.toUTF8
  = .ok parsedProof := sorry

-- Just to keepthe goal state tidy
syntax "λ" : term
open Lean PrettyPrinter Delaborator in
@[delab lam]
def delabLam : Delab := `(λ)

-- #eval ex._reflection_def_1

example : ex._reflection_def_1 = true := by
  unfold ex._reflection_def_1
  unfold Std.Tactic.BVDecide.Reflect.verifyBVExpr
  unfold Std.Tactic.BVDecide.Reflect.verifyCert
  rw [parse_aux]
  dsimp
  conv =>
    enter [1,2,1,1]
    unfold ex._expr_def_1
    simp -underLambda -zeta -zetaDelta [
      Std.Tactic.BVDecide.BVLogicalExpr.bitblast,
      Std.Tactic.BVDecide.ofBoolExprCached,
      Std.Sat.AIG.empty,
      Std.Tactic.BVDecide.ofBoolExprCached.go,
      Std.Tactic.BVDecide.BVPred.bitblast,
      Std.Tactic.BVDecide.BVExpr.bitblast,
      Std.Tactic.BVDecide.BVExpr.bitblast.go,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastConst,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastVar,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastVar.go,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastMul,
      Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go

    ]



-- #print ex._reflection_def_1
-- #eval Std.Sat.AIG.toCNF (Std.Tactic.BVDecide.BVLogicalExpr.bitblast ex._expr_def_1).relabelNat
