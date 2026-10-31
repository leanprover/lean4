/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Std.Tactic.BVDecide.LRAT.Parser
public import Lean.CoreM
public import Std.Tactic.BVDecide.Syntax
public import Lean.Cadical.Basic

/-!
This module implements the logic to call CaDiCal (or CLI interface compatible SAT solvers) and
extract an LRAT UNSAT proof or a model from its output.
-/

namespace Lean.Meta.Tactic.BVDecide

namespace External

open Std.Tactic.BVDecide

/--
The result of calling a SAT solver.
-/
public inductive SolverResult where
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

public inductive TimedOut (α : Type u) where
  | success (x : α)
  | timeout

/--
Run a process with `args` until it terminates or the cancellation token in `CoreM` tells us to abort
or `timeout` seconds have passed.
-/
public partial def runInterruptible (timeout : Nat) (args : IO.Process.SpawnArgs) :
    CoreM (TimedOut IO.Process.Output) := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  go (timeout * 1000) 1 64 child stdout stderr
where
  go {cfg} (budgetMs sleepMs maxSleepMs : Nat) (child : IO.Process.Child cfg)
      (stdout stderr : Task (Except IO.Error String)) : CoreM (TimedOut IO.Process.Output) := do
    let cleanup := killAndWait child
    withTimeoutCheck budgetMs cleanup do
    withInterruptCheck cleanup do
      -- TODO: replace me with a select once we get libuv process support
      match ← child.tryWait with
      | some exitCode =>
        let stdout ← IO.ofExcept stdout.get
        let stderr ← IO.ofExcept stderr.get
        return .success { exitCode := exitCode, stdout := stdout, stderr := stderr }
      | none =>
        IO.sleep sleepMs.toUInt32
        let nextSleepMs := if sleepMs ≥ maxSleepMs then sleepMs else sleepMs * 2
        go (budgetMs - sleepMs) nextSleepMs maxSleepMs child stdout stderr

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
        throwInterruptException
    x

public def throwSatTimeout : CoreM α := do
  let mut err := "The SAT solver timed out while solving the problem.\n"
  err := err ++ "Consider increasing the timeout with the `timeout` config option.\n"
  err := err ++ "If solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option."
  throwError err

public structure SatOptions where
  configuration : String
  longOptions : Array String
  options : Array (String × Int32)

namespace SatOptions

public def ofMode (mode : Elab.Tactic.BVDecide.SolverMode) : SatOptions :=
  {
    configuration :=
      match mode with
      | .proof => "unsat"
      | .counterexample => "sat"
      | .default => "default"
    longOptions := #[]
    options :=
      /-
      Bitwuzla sets this option and it does improve performance practically:
      https://github.com/bitwuzla/bitwuzla/blob/0e81e616af4d4421729884f01928b194c3536c76/src/sat/cadical.cpp#L34
      -/
      #[("shrink", 0)]
  }

public def addLrat (opts : SatOptions) (binary : Bool) : SatOptions :=
  { opts with
      longOptions := opts.longOptions ++ #["lrat", "quiet"]
      options := opts.options.push ("binary", binary.toUInt32.toInt32)
  }

public def addIncremental (opts : SatOptions) : SatOptions :=
  { opts with
      options := opts.options.push ("ilb", 2)
  }

public def toArgs (opts : SatOptions) : Array String := Id.run do
  let mut args := #[]
  args := args.push <| flag opts.configuration
  for longOpt in opts.longOptions do
    args := args.push <| flag longOpt
  for (opt, val) in opts.options do
    args := args.push  <| flagValue opt val
  return args
where
  flag (opt : String) : String := s!"--{opt}"
  flagValue (opt : String) (val : Int32) : String := s!"--{opt}={val}"

public def configureSolver (opts : SatOptions) (solver : Cadical.Solver) : BaseIO Unit := do
  discard <| solver.configure opts.configuration
  for longOpt in opts.longOptions do
    discard <| solver.setLongOption longOpt
  for (opt, val) in opts.options do
    discard <| solver.setOption opt val

end SatOptions

/--
Call the SAT solver in `solverPath` with `problemPath` as CNF input and ask it to output an LRAT
UNSAT proof (binary or non-binary depending on `binaryProofs`) into `proofOutput`. To avoid runaway
solvers the solver is run with `timeout` in seconds as a maximum time limit to solve the problem.

Note: This function currently assume that the solver has the same CLI as CaDiCal.
-/
public def satQuery (solverPath : System.FilePath) (problemPath : System.FilePath) (proofOutput : System.FilePath)
    (timeout : Nat) (binaryProofs : Bool) (mode : Elab.Tactic.BVDecide.SolverMode) :
    CoreM SolverResult := do
  let options := SatOptions.ofMode mode |>.addLrat binaryProofs
  let cmd := solverPath.toString
  let args := #[ problemPath.toString, proofOutput.toString] ++ options.toArgs

  -- We implement timeouting ourselves because cadicals -t option is not available on Windows.
  let out? ← runInterruptible timeout { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
  match out? with
  | .timeout => throwSatTimeout
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
        throwError s!"The external prover produced unexpected output, stdout:\n{stdout}\nstderr:\n{stderr}"

end External

end Lean.Meta.Tactic.BVDecide
