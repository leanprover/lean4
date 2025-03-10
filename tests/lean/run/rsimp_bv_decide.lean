import Std.Tactic.BVDecide
import Std.Tactic.RSimp
import Std.Tactic.RSimp.ConvTheorem

theorem ex (i : BitVec 5) : 2 * i &&& 1 = 0 := by bv_decide

/-- info: true -/
#guard_msgs in
#eval ex._reflection_def_1

-- #print ex._expr_def_1
-- #print ex._cert_def_1

open Lean in
partial def callPaths (source : Name) (target : Name) : CoreM MessageData := do
  let rec go (n : Name) : StateT (NameMap Bool) CoreM (Option MessageData) := do
    if n = target then
      return m!"{.ofConstName n} !"
    if let some hit := (← get).find? n then
      if hit then
        return m!"{.ofConstName n} ↑"
    let .defnInfo ci ← getConstInfo n | return none
    let ns := Expr.getUsedConstants ci.value
    let ms ← ns.filterMapM go
    let hit := !ms.isEmpty
    modify (·.insert n hit)
    unless hit do return none
    return some <| .ofConstName n ++ (.nest 1 ("\n" ++ (.joinSep ms.toList "\n")))

  if let some md ← (go source).run' {} then
    pure md
  else
    pure "No paths from {.ofConstName source} to {.ofConstName target} found"

open Lean Elab Command in
elab "#call_paths " i1:ident " => " i2:ident : command => liftTermElabM do
    let source ← realizeGlobalConstNoOverloadWithInfo i1
    let target ← realizeGlobalConstNoOverloadWithInfo i2
    let m ← callPaths source target
    logInfo m


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

@[rsimp] theorem parse_aux :
  Std.Tactic.BVDecide.LRAT.parseLRATProof ex._cert_def_1.toUTF8
  = .ok parsedProof := sorry

attribute [rsimp_optimize] Std.Tactic.BVDecide.BVExpr.bitblast.blastConst.go
attribute [rsimp_optimize] Std.Tactic.BVDecide.BVExpr.bitblast.blastConst
attribute [rsimp_optimize] Std.Tactic.BVDecide.BVExpr.bitblast.go
attribute [rsimp_optimize] Std.Tactic.BVDecide.BVExpr.bitblast
attribute [rsimp_optimize] Std.Tactic.BVDecide.LRAT.Internal.Formula.performRupAdd
attribute [rsimp_optimize] List.filterMap
attribute [rsimp_optimize] Std.Sat.AIG.Entrypoint.relabelNat
attribute [rsimp_optimize] Std.Sat.AIG.toCNF
attribute [rsimp_optimize] Std.Sat.CNF.numLiterals
attribute [rsimp_optimize] Std.Tactic.BVDecide.LRAT.Internal.intActionToDefaultClauseAction
attribute [rsimp_optimize] Std.Tactic.BVDecide.LRAT.Internal.CNF.convertLRAT
attribute [rsimp_optimize] Std.Tactic.BVDecide.LRAT.Internal.lratChecker
attribute [rsimp_optimize] Std.Tactic.BVDecide.ofBoolExprCached
set_option trace.tactic.rsimp_optimize true in
-- This doesn't rewrite BVExpr.bitblast because it's dependent
-- attribute [rsimp_optimize] Std.Tactic.BVDecide.BVPred.bitblast

-- Also doesnt work, due to abstracted proofs
set_option pp.proofs true in
conv_theorem bitblast_opt : Std.Tactic.BVDecide.BVPred.bitblast =>
  unfold Std.Tactic.BVDecide.BVPred.bitblast
  unfold Std.Tactic.BVDecide.BVPred.bitblast.proof_1
  simp -zeta [Std.Tactic.BVDecide.BVExpr.bitblast.eq_rsimp]

attribute [rsimp_optimize] Std.Tactic.BVDecide.BVLogicalExpr.bitblast
attribute [rsimp_optimize] Std.Tactic.BVDecide.LRAT.check
attribute [rsimp_optimize] Std.Tactic.BVDecide.Reflect.verifyCert
attribute [rsimp_optimize] Std.Tactic.BVDecide.Reflect.verifyBVExpr
attribute [rsimp_optimize] ex._reflection_def_1


@[rsimp] conv_theorem unfold_to_parser :
    ex._reflection_def_1 =>
  simp [ex._reflection_def_1, Std.Tactic.BVDecide.Reflect.verifyBVExpr,
    Std.Tactic.BVDecide.Reflect.verifyCert, rsimp]
  abstractAs optimized_reflection_def

#call_paths optimized_reflection_def =>  WellFounded.fix

-- #print optimized_reflection_def

open Lean Meta in
elab "#kernel_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  Lean.Meta.lambdaTelescope e fun _ e => do
    -- let e' ← Lean.ofExceptKernelException <| Lean.Kernel.whnf (← Lean.getEnv) (← Lean.getLCtx) e
    let e' ← withOptions (smartUnfolding.set ·  false) <| withTransparency .all <| Lean.Meta.whnf e
    Lean.logInfo m!"{e'}"

open Std.Tactic.BVDecide.LRAT

-- #kernel_reduce ex._reflection_def_1
-- /-- info: true -/ #guard_msgs in #eval optimized_reflection_def

syntax "λ" : term

open Lean PrettyPrinter Delaborator in
@[delab lam]
def delabLam : Delab := `(λ)

set_option diagnostics true
set_option diagnostics.threshold 0
#kernel_reduce optimized_reflection_def

-- #print ex._reflection_def_1
-- #eval Std.Sat.AIG.toCNF (Std.Tactic.BVDecide.BVLogicalExpr.bitblast ex._expr_def_1).relabelNat
