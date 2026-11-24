/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Ullrich
-/
import Lean.Replay
import LeanExport.Parse

open Lean

def println (msg : String) (silent : Bool) : IO Unit :=
  unless silent do
    IO.println msg

def checkExport (args : List String) (silent : Bool) : IO UInt32 := do
  let [exportFile] := args |
    throw <| IO.userError s!"Exactly one export file expected but got: {args}"
  IO.FS.withFile exportFile .read fun handle => do
    let exportEnv ← LeanExport.parseStream (.ofHandle handle)
    let env ← Lean.mkEmptyEnvironment
    let mut kernelEnv := env.toKernelEnv
    let origConstMap := exportEnv.constMap
    -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
    -- multiple times leads to errors.
    let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
    let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
    try
      kernelEnv ← kernelEnv.replay kernelConstMap
      println "Lean default kernel accepts the solution" silent
    catch e =>
      println s!"Lean default kernel rejects the solution: {e}" silent
      return 1

    try
      let verifyTargets := `Quot :: quotTargets
      for quotTarget in verifyTargets do
        if let some info := origConstMap[quotTarget]? then
          let some info' := kernelEnv.find? quotTarget |
            throw <| .userError s!"Could not find quotient constant in final kernel env: {quotTarget}"
          if info != info' then
            throw <| IO.userError s!"Quotient constant mismatch on: {quotTarget}"
      return 0
    catch e =>
      println s!"Quotient post-check rejects the solution: {e}" silent
      return 1

/--
Run as `leanchecker --from-export FILE` to replay all declarations of the given `leanexport` output
into a fresh environment, using the kernel to check them. `--silent` suppresses all output but the
exit code.
-/
def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition fun s => s.startsWith "-"
  unless "--from-export" ∈ flags do
    throw <| IO.userError "usage: leanchecker [--silent] --from-export FILE"
  checkExport args ("--silent" ∈ flags)
