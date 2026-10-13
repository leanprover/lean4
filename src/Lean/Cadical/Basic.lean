/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Lean.Cadical.Internal
public import Std.Sat.CNF.Basic
public import Init.Data.SInt.Basic
public import Init.System.IO

namespace Lean.Cadical

/-!
This module provides a thin wrapper around CaDiCaL's C++ FFI, allowing it to interact with the CNF
API from `Std.Sat.CNF`.
-/

/--
The IPASIR state of the solver.
-/
public structure State where
  bits : UInt16
  deriving Inhabited, DecidableEq, Hashable

namespace State

@[inline]
public def initializing : State := ⟨1⟩

@[inline]
public def configuring : State := ⟨2⟩

@[inline]
public def steady : State := ⟨4⟩

@[inline]
public def adding : State := ⟨8⟩

@[inline]
public def solving : State := ⟨16⟩

@[inline]
public def satisfied : State := ⟨32⟩

@[inline]
public def unsatisfied : State := ⟨64⟩

@[inline]
public def deleting : State := ⟨128⟩

@[inline]
public def inconclusive : State := ⟨256⟩

@[inline]
def ready : State :=
  ⟨
    configuring.bits
      ||| steady.bits
      ||| satisfied.bits
      ||| unsatisfied.bits
      ||| inconclusive.bits
  ⟩

@[inline]
def valid : State :=
  ⟨ready.bits ||| adding.bits⟩

@[inline]
def invalid : State :=
  ⟨initializing.bits ||| deleting.bits⟩

@[inline]
public def isReady (s : State) : Bool := (s.bits &&& ready.bits) != ⟨0⟩

@[inline]
public def isValid (s : State) : Bool := (s.bits &&& valid.bits) != ⟨0⟩

@[inline]
public def isInvalid (s : State) : Bool := (s.bits &&& invalid.bits) != ⟨0⟩

public def toString (s : State) : String :=
  if s == .initializing then
    "INITIALIZING"
  else if s == .configuring then
    "CONFIGURING"
  else if s == .steady then
    "STEADY"
  else if s == .adding then
    "ADDING"
  else if s == .solving then
    "SOLVING"
  else if s == .satisfied then
    "SATISFIED"
  else if s == .unsatisfied then
    "UNSATISFIED"
  else if s == .inconclusive then
    "INCONCLUSIVE"
  else
    "INVALID_STATE"

public instance : ToString State where
  toString := toString

end State

public inductive Status where
  | satisfiable
  | unsatisfiable
  | unknown
  deriving Inhabited, DecidableEq, Hashable, Repr

namespace Status

public def toInt32 : Status → Int32
  | .satisfiable => 10
  | .unsatisfiable => 20
  | .unknown => 0

public def toString : Status → String
  | .satisfiable => "SAT"
  | .unsatisfiable => "UNSAT"
  | .unknown => "UNKNOWN"

public instance : ToString Status where
  toString := Status.toString

@[inline]
def ofInternal (s : Internal.Status) : Status :=
  match s with
  | .satisfiable => .satisfiable
  | .unsatisfiable => .unsatisfiable
  | .unknown => .unknown

end Status

/--
An incremental SAT solver.
-/
public structure Solver where
  private ofNative ::
    private solver : Internal.Solver
  deriving Nonempty

namespace Solver

open Std.Sat

@[inline]
def toApiLit (lit : Nat) (pol : Bool) : IO Int32 := do
  let lit := lit + 1
  if lit > Int32.maxValue.toNatClampNeg then
    throw <| .userError "Literal {lit} too large for SAT API"
  else
    let lit := lit.toInt32
    let lit := if pol then lit else -lit
    return lit

/--
Allocate a new SAT solver.
-/
public def new : BaseIO Solver := return ⟨← Internal.Solver.new⟩


/--
Get the current IPASIR state of the solver.
-/
public def state (s : Solver) : BaseIO State := return ⟨← s.solver.state⟩

/--
Add a clause to the solver.
-/
public def clause (s : Solver) (clause : CNF.Clause Nat) : IO Unit := do
  assert! (← s.state).isValid
  for (lit, pol) in clause do
    let lit ← toApiLit lit pol
    s.solver.add lit
  s.solver.add 0

/--
Check whether the formula is currently inconsistent (potentially under assumptions).
-/
public def inconsistent (s : Solver) : BaseIO Bool := s.solver.inconsistent

/--
Add a new assumption literal to the solver, reset upon the next call to `solve`.
-/
public def assume (s : Solver) (lit : Nat) (pol : Bool) : IO Unit := do
  assert! (← s.state).isReady
  s.solver.assume (← toApiLit lit pol)

/--
Run the SAT solver on current formula and assumptions.
-/
public def solve (s : Solver) : BaseIO Status := do
  assert! (← s.state).isReady
  let status ← s.solver.solve
  return .ofInternal status

/--
Obtain the value of a literal in the current model if it exists.
-/
public def val (s : Solver) (lit : Nat) : IO Bool := do
  let state ← s.state
  if state != .satisfied then
    throw <| .userError s!"State should be {State.satisfied} but is {state}"
  let lit ← toApiLit lit true
  let val ← s.solver.val lit
  return lit == val

/--
Reset assumptions made via `assume` explicitily.
-/
public def resetAssumptions (s : Solver) : BaseIO Unit :=
  s.solver.resetAssumptions

/--
Query the current status (not to be confused with the IPASIR state) of the oslver.
-/
public def status (s : Solver) : BaseIO Status := do
  let status ← s.solver.status
  return .ofInternal status

public def isValidOption (opt : String) : Bool := Internal.Solver.isValidOption opt

public def isPreprocessingOption (opt : String) : Bool := Internal.Solver.isPreprocessingOption opt

public def isValidLongOption (opt : String) : Bool := Internal.Solver.isValidLongOption opt

public def getOption (s : Solver) (opt : String) : BaseIO Int32 := s.solver.get opt

public def setOption (s : Solver) (opt : String) (val : Int32) : BaseIO Bool := do
  assert! (← s.state) == .configuring
  s.solver.set opt val

public def setLongOption (s : Solver) (opt : String) : BaseIO Bool := do
  assert! (← s.state) == .configuring
  s.solver.setLongOption opt

public def isValidConfiguration (opt : String) : Bool := Internal.Solver.isValidConfiguration opt

public def configure (s : Solver) (opt : String) : BaseIO Bool := do
  assert! (← s.state) == .configuring
  s.solver.configure opt

public def terminate (s : Solver) : BaseIO Unit := do
  let state ← s.state
  assert! state == .solving || state.isReady
  s.solver.terminate

public def printConfigurations : IO Unit := Internal.Solver.configurations

public def printStatistics (s : Solver) : IO Unit := s.solver.statistics

public def printResources (s : Solver) : IO Unit := s.solver.resources

end Solver

end Lean.Cadical
