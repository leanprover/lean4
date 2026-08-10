/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Main
public import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Tactic.BVDecide.LRAT.Trim
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Grind.Main

public section

/-!
This module offers three different SAT tactics for proving goals involving `BitVec` and `Bool`:
1. `bv_decide` takes the goal, hands it over to a SAT solver and verifies the generated LRAT
   UNSAT proof to prove the goal.
2. `bv_check file.lrat` can prove the same things as `bv_decide`. However instead of
   dynamically handing the goal to a SAT solver to obtain an LRAT proof, the LRAT proof is read from
   `file.lrat`. This allows users that do not have a SAT solver installed to verify proofs.
3. `bv_decide?` offers a code action to turn a `bv_decide` invocation automatically into a
   `bv_check` one.

Additionally it offers `bv_normalize`, which only runs the preprocessing of the tactics above.

There are also some options to influence the behavior of `bv_decide` and friends:
- `sat.solver`: the name of the SAT solver used by `bv_decide`. It goes through 3 steps to determine
   which solver to use:
   1. If sat.solver is set to something != "" it will use that.
   2. If sat.solver is set to "" it will check if there is a cadical binary next to the executing
      program. Usually that program is going to be `lean` itself and we do ship a `cadical` next to it.
   3. If that does not succeed try to call `cadical` from PATH.
- `sat.timeout`: The timeout for waiting for the SAT solver in seconds, default 10.
- `sat.trimProofs`: Whether to run the trimming algorithm on LRAT proofs, default true.
- `sat.binaryProofs`: Whether to use the binary LRAT proof format, default true.
- `trace.Meta.Tactic.bv` and `trace.Meta.Tactic.sat` for inspecting the inner workings of `bv_decide`.
- `debug.skipKernelTC`: may be set to true to disable actually checking the LRAT proof.
  `bv_decide` will still run bitblasting + SAT solving so this option essentially trusts the SAT
  solver.

## Architecture
`bv_decide` roughly runs through the following steps:
1. Apply `false_or_by_contra` to start a proof by contradiction.
2. Apply the `bv_normalize` and `seval` simp set to all hypotheses. This has two effects:
    1. It applies a subset of the rewrite rules from [Bitwuzla](https://github.com/bitwuzla/bitwuzla)
       for simplification of the expressions.
    2. It turns all hypotheses that might be of interest for the remainder of the tactic into the form
       `x = true` where `x` is a mixture of `Bool` and fixed width `BitVec` expressions.
3. Use proof by reflection to reduce the proof to showing that an SMT-LIB-syntax-like value that
   represents the conjunction of all relevant assumptions is UNSAT.
4. Use a verified bitblasting algorithm to turn that expression into an AIG.
   The bitblasting algorithms are collected from various other bitblasters, including Bitwuzla and
   Z3 and verified using Lean's `BitVec` theory.
5. Turn the AIG into a CNF.
6. Run CaDiCal on the CNF to obtain an LRAT proof that the CNF is UNSAT. If CaDiCal returns SAT
   instead the tactic aborts here and presents a counterexample.
7. Use an LRAT checker with a soundness proof in Lean to show that the LRAT proof is correct.
8. Chain all the proofs so far to demonstrate that the original goal holds.

## Axioms
`bv_decide` makes use of proof by reflection and adds the result of the compiled check as an axoim,
thus adding the Lean compiler to the trusted code base.


## Adding a new primitive
`bv_decide` knows two kinds of primitives:
1. The ones that can be reduced to already existing ones.
2. The ones that cannot.

For the first kind the steps to adding them are very simple, go to `Std.Tactic.BVDecide.Normalize`
and add the reduction lemma into the `bv_normalize` simp set. Don't forget to add a test!

For the second kind more steps are involved:
1. Add a new constructor to `BVExpr`/`BVPred`
2. Add a bitblasting algorithm for the new constructor to `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl`.
3. Verify that algorithm in `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas`.
4. Integrate it with either the expression or predicate bitblaster and use the proof above to verify it.
5. Add simplification lemmas for the primitive to `bv_normalize` in `Std.Tactic.BVDecide.Normalize`.
   If there are multiple ways to write the primitive (e.g. with TC based notation and without) you
   should normalize for one notation here.
6. Add the reflection code to `Lean.Meta.Tactic.BVDecide.Reflect`
7. Add a test!
-/

namespace Lean.Elab.Tactic.BVDecide

def ensureBvDecide : CoreM Unit := do
  let env ← getEnv
  if (env.getModuleIdx? `Std.Tactic.BVDecide).isNone then
    throwError "to use `bv_decide`, please include `import Std.Tactic.BVDecide`"

namespace BVCheck

open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Meta Tactic.BVDecide

/--
Get the directory that contains the Lean file which is currently being elaborated.
-/
def getSrcDir : TermElabM System.FilePath := do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  return srcDir

def mkContext (lratPath : System.FilePath) (cfg : BVDecideConfig)
    (types : Option (Array Name) := none) : TermElabM TacticContext := do
  let lratPath := (← getSrcDir) / lratPath
  TacticContext.new lratPath cfg types

@[inherit_doc Lean.Parser.Tactic.bvCheck]
def bvCheck (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext) :
    Meta.Sym.SymM Unit := do
  M.run (hypotheses := hypotheses) do
    discard <| closeWithBVReflection g (lratChecker ctx)

def evalBvCheck (target : Normalize.Target) (ctx : TacticContext) (warn : MetaM Unit) :
    Grind.GrindM Unit := do
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    if ← Normalize.bvNormalize then
      warn
    else
      bvCheck (← Normalize.PreProcessM.getTargetMVarId) (← Normalize.PreProcessM.getHyps) ctx

end BVCheck

namespace BVTrace

open Std.Tactic.BVDecide.LRAT
open Meta Tactic BVDecide

-- TODO: think of a more maintainable file pattern for this stuff.
/--
Produce a file with the pattern:
LeanFileName-DeclName-Line-Col.lrat
-/
def getLratFileName : TermElabM System.FilePath := do
  let some baseName := System.FilePath.mk (← getFileName) |>.fileName | throwError "could not find file name"
  let some declName ← Term.getDeclName? | throwError "could not find declaration name"
  let pos := (← getFileMap).toPosition (← getRefPos)
  return s!"{baseName}-{declName}-{pos.line}-{pos.column}.lrat"

def mkContext (cfg : BVDecideConfig) (types : Option (Array Name) := none) :
    TermElabM TacticContext := do
  let lratPath ← getLratFileName
  BVCheck.mkContext lratPath cfg types

inductive TraceResult where
  | normalize
  | check (path : System.FilePath)

def evalBvTrace (target : Normalize.Target) (ctx : TacticContext) : Grind.GrindM TraceResult := do
  let trace ← target.mvarId.withContext do
    bvDecide target { ctx with config := { ctx.config with trimProofs := false } }
  /-
  Ideally trace.lratCert would be the `ByteArray` version of the proof already and we just write
  it. This isn't yet possible so instead we do the following:
  1. Produce the proof in the tactic.
  2. Skip trimming it in the tactic.
  3. Run trimming on the LRAT file that was produced by the SAT solver directly, emitting the
     correct binary format according to `sat.binaryProofs`.
  TODO: Fix this hack:
  1. Introduce `ByteArray` literals to the kernel.
  2. Just return the fully trimmed proof in the format desired by the configuration from `bvDecide`.
  3. Write it to the file directly.
  -/
  match trace.lratCert with
  | none =>
    return .normalize
  | some .. =>
    if ctx.config.trimProofs then
      let proof ← loadLRATProof ctx.lratPath
      let trimmed ← IO.ofExcept <| LRAT.trim proof
      dumpLRATProof ctx.lratPath trimmed ctx.config.binaryProofs
    let some lratFile := ctx.lratPath.fileName | throwError "could not find file name"
    return .check lratFile

end BVTrace

open Meta Tactic.BVDecide

@[builtin_tactic Lean.Parser.Tactic.bvDecide]
def evalBvDecide : Tactic := fun
  | `(tactic| bv_decide $cfg:optConfig $[$types:bvTypes]?) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfg
    let types ← elabBVDecideTypes types
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg types
      liftMetaFinishingTactic fun g => do
        let params ← Grind.mkDefaultParams {}
        discard <| Grind.GrindM.run (params := params) <| bvDecide (.mvarIdTarget g) cfg
  | _ => throwUnsupportedSyntax

open Lean.Meta.Tactic in
@[builtin_tactic Lean.Parser.Tactic.bvTrace]
def evalBvTraceTactic : Tactic := fun
  | `(tactic| bv_decide?%$tk $cfgStx:optConfig $[$typesStx:bvTypes]?) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfgStx
    let types ← elabBVDecideTypes typesStx
    let ctx ← BVTrace.mkContext cfg types
    let g ← getMainGoal
    let params ← Grind.mkDefaultParams {}
    Grind.GrindM.run (params := params) do
      match ← BVTrace.evalBvTrace (.mvarIdTarget g) ctx with
      | .normalize =>
        let normalizeStx ← `(tactic| bv_normalize $cfgStx:optConfig $[$typesStx:bvTypes]?)
        TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
      | .check lratFile =>
        let bvCheckStx ←
          `(tactic| bv_check $cfgStx:optConfig $[$typesStx:bvTypes]? $(quote lratFile.toString))
        TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

open Lean.Meta.Tactic in
@[builtin_tactic Lean.Parser.Tactic.bvCheck]
def evalBvCheckTactic : Tactic := fun
  | `(tactic| bv_check%$tk $cfgStx:optConfig $[$typesStx:bvTypes]? $path:str) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfgStx
    let types ← elabBVDecideTypes typesStx
    let ctx ← BVCheck.mkContext path.getString cfg types
    let g ← getMainGoal
    let params ← Grind.mkDefaultParams {}
    Grind.GrindM.run (params := params) <| BVCheck.evalBvCheck (.mvarIdTarget g) ctx do
      let bvNormalizeStx ← `(tactic| bv_normalize $cfgStx $[$typesStx:bvTypes]?)
      logWarning m!"This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."
      TryThis.addSuggestion tk bvNormalizeStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.bvNormalize]
def evalBVNormalize : Tactic := fun
  | `(tactic| bv_normalize $cfg:optConfig $[$types:bvTypes]?) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfg
    let types ← elabBVDecideTypes types
    let g ← getMainGoal
    let params ← Grind.mkDefaultParams {}
    let (_, state) ← Grind.GrindM.run (params := params) do
      Normalize.bvNormalize.run { config := cfg, restrictedTypes := types } (.mvarIdTarget g)
    let goal := state.target.mvarId
    if ← goal.isAssigned then
      replaceMainGoal []
    else
      let hyps := state.hypotheses.map fun hyp => {
        userName := hyp.name
        type := hyp.type
        value := hyp.value
      }
      let (_, goal) ← MVarId.assertHypotheses goal hyps
      replaceMainGoal [goal]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.BVDecide
