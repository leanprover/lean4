/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.CoreM
import Std.Internal.Parsec

/-!
This module implements the logic to call CaDiCal (or CLI interface compatible SAT solvers) and
extract an LRAT UNSAT proof or a model from its output.
-/

namespace Lean.Elab.Tactic.BVDecide

namespace External

open Std.Tactic.BVDecide

/--
The result of calling a SAT solver.
-/
inductive SolverResult where
  /--
  The solver returned SAT with some literal assignment.
  -/
  | sat (assignment : Array (Bool × Nat))
  /--
  The solver returned UNSAT.
  -/
  | unsat

namespace ModelParser

open Std.Internal.Parsec
open Std.Internal.Parsec.ByteArray
open LRAT.Parser.Text (skipNewline)

def parsePartialAssignment : Parser (Bool × (Array (Bool × Nat))) := do
  skipByteChar 'v'
  let idents ← many (attempt wsLit)
  let idents := idents.map (fun i => if i > 0 then (true, i.natAbs) else (false, i.natAbs))
  tryCatch
    (skipString " 0")
    (csuccess := fun _ => pure (true, idents))
    (cerror := fun _ => do
      skipNewline
      return (false, idents)
    )
where
  @[inline]
  wsLit : Parser Int := do
    skipByteChar ' '
    LRAT.Parser.Text.parseLit

partial def parseLines : Parser (Array (Bool × Nat)) :=
  go #[]
where
  go (acc : Array (Bool × Nat)) : Parser (Array (Bool × Nat)) := do
    let (terminal?, additionalAssignment) ← parsePartialAssignment
    let acc := acc ++ additionalAssignment
    if terminal? then
      return acc
    else
      go acc

@[inline]
def parseHeader : Parser Unit := do
  skipString "s SATISFIABLE"
  skipNewline

/--
Parse the witness format of a SAT solver. The rough grammar for this is:
line = "v" (" " lit)*\n
terminal_line = "v" (" " lit)* (" " 0)\n
witness = "s SATISFIABLE\n" line+ terminal_line
-/
def parse : Parser (Array (Bool × Nat)) := do
  parseHeader
  parseLines

end ModelParser

open Lean (CoreM)

inductive TimedOut (α : Type u) where
  | success (x : α)
  | timeout

/--
Run a process with `args` until it terminates or the cancellation token in `CoreM` tells us to abort
or `timeout` seconds have passed.
-/
partial def runInterruptible (timeout : Nat) (args : IO.Process.SpawnArgs) :
    CoreM (TimedOut IO.Process.Output) := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  go (timeout * 1000) child stdout stderr
where
  go {cfg} (budgetMs : Nat) (child : IO.Process.Child cfg) (stdout stderr : Task (Except IO.Error String)) :
      CoreM (TimedOut IO.Process.Output) := do
    let cleanup := killAndWait child
    withTimeoutCheck budgetMs cleanup do
    withInterruptCheck cleanup do
      match ← child.tryWait with
      | some exitCode =>
        let stdout ← IO.ofExcept stdout.get
        let stderr ← IO.ofExcept stderr.get
        return .success { exitCode := exitCode, stdout := stdout, stderr := stderr }
      | none =>
        let sleepMs : Nat := 50
        IO.sleep sleepMs.toUInt32
        go (budgetMs - sleepMs) child stdout stderr

  killAndWait {cfg} (child : IO.Process.Child cfg) : IO Unit := do
    child.kill
    discard child.wait

  withTimeoutCheck {α : Type} (budgetMs : Nat) (cleanup : CoreM Unit) (x : CoreM (TimedOut α)) :
      CoreM (TimedOut α) := do
    if budgetMs == 0 then
      cleanup
      return .timeout
    else
      x

  withInterruptCheck {α : Type} (cleanup : CoreM Unit) (x : CoreM α) :
      CoreM α := do
    if let some tk := (← read).cancelTk? then
      if ← tk.isSet then
        cleanup
        throw <| .internal Core.interruptExceptionId
    x

/--
Call the SAT solver in `solverPath` with `problemPath` as CNF input and ask it to output an LRAT
UNSAT proof (binary or non-binary depending on `binaryProofs`) into `proofOutput`. To avoid runaway
solvers the solver is run with `timeout` in seconds as a maximum time limit to solve the problem.

Note: This function currently assume that the solver has the same CLI as CaDiCal.
-/
def satQuery (solverPath : System.FilePath) (problemPath : System.FilePath) (proofOutput : System.FilePath)
    (timeout : Nat) (binaryProofs : Bool) :
    CoreM SolverResult := do
  let cmd := solverPath.toString
  let mut args := #[
    problemPath.toString,
    proofOutput.toString,
    "--lrat",
    s!"--binary={binaryProofs}",
    "--quiet",
    /-
    This sets the magic parameters of cadical to optimize for UNSAT search.
    Given the fact that we are mostly interested in proving things and expect user goals to be
    provable this is a fine value to set
    -/
    "--unsat",
    /-
    Bitwuzla sets this option and it does improve performance practically:
    https://github.com/bitwuzla/bitwuzla/blob/0e81e616af4d4421729884f01928b194c3536c76/src/sat/cadical.cpp#L34
    -/
    "--shrink=0"
  ]

  -- We implement timeouting ourselves because cadicals -t option is not available on Windows.
  let out? ← runInterruptible timeout { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
  match out? with
  | .timeout =>
    let mut err := "The SAT solver timed out while solving the problem.\n"
    err := err ++ "Consider increasing the timeout with the `timeout` config option.\n"
    err := err ++ "If solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option."
    throwError err
  | .success { exitCode := exitCode, stdout := stdout, stderr := stderr} =>
    if exitCode == 255 then
      throwError s!"Failed to execute external prover:\n{stderr}"
    else
      if stdout.startsWith "s UNSATISFIABLE" then
        return .unsat
      else if stdout.startsWith "s SATISFIABLE" then
        match ModelParser.parse.run stdout.toUTF8 with
        | .ok assignment =>
          return .sat assignment
        | .error err =>
          throwError s!"Error {err} while parsing:\n{stdout}"
      else
        throwError s!"The external prover produced unexpected output, stdout:\n{stdout}stderr:\n{stderr}"

end External

end Lean.Elab.Tactic.BVDecide
