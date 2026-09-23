/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Bootstrap
public import Init.Data.SInt.Basic
public import Init.System.IO

/-!
This module provides CaDiCaL's C++ FFI in Lean.
See https://github.com/arminbiere/cadical/blob/rel-2.2.1/src/cadical.hpp for precise usage
information and invariants.
-/


namespace Lean.Cadical.Internal

opaque SolverImpl : NonemptyType.{0}

public inductive Status where
  | satisfiable
  | unsatisfiable
  | unknown
  deriving Inhabited, DecidableEq, Hashable, Repr

public def Status.toInt32 : Status → Int32
  | .satisfiable => 10
  | .unsatisfiable => 20
  | .unknown => 0

@[extern "lean_cadical_signature"]
opaque getSignature (u : Unit) : String

public def signature : String := getSignature ()

public def Solver : Type := SolverImpl.type

public instance : Nonempty Solver := SolverImpl.property

namespace Solver

@[extern "lean_cadical_solver_new"]
public opaque new : BaseIO Solver

@[extern "lean_cadical_solver_add"]
public opaque add (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_clause"]
public opaque clause (s : @& Solver) (lits : @& Array Int32) : BaseIO Unit

@[extern "lean_cadical_solver_inconsistent"]
public opaque inconsistent (s : @& Solver) : BaseIO Bool

@[extern "lean_cadical_solver_assume"]
public opaque assume (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_solve"]
public opaque solve (s : @& Solver) : BaseIO Status

@[extern "lean_cadical_solver_val"]
public opaque val (s : @& Solver) (lit : Int32) : BaseIO Int32

@[extern "lean_cadical_solver_flip"]
public opaque flip (s : @& Solver) (lit : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_flippable"]
public opaque flippable (s : @& Solver) (lit : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_failed"]
public opaque failed (s : @& Solver) (lit : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_constrain"]
public opaque constrain (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_constraint_failed"]
public opaque constraintFailed (s : @& Solver) : BaseIO Bool

@[extern "lean_cadical_solver_lookahead"]
public opaque lookahead (s : @& Solver) : BaseIO Int32

@[extern "lean_cadical_solver_reset_assumptions"]
public opaque resetAssumptions (s : @& Solver) : BaseIO Unit

@[extern "lean_cadical_solver_reset_constraint"]
public opaque resetConstraint (s : @& Solver) : BaseIO Unit

@[extern "lean_cadical_solver_status"]
public opaque status (s : @& Solver) : BaseIO Status

@[extern "lean_cadical_solver_vars"]
public opaque vars (s : @& Solver) : BaseIO Int32

@[extern "lean_cadical_solver_resize"]
public opaque resize (s : @& Solver) (minMaxVar : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_is_valid_option"]
public opaque isValidOption (opt : @& String) : Bool

@[extern "lean_cadical_solver_is_preprocessing_option"]
public opaque isPreprocessingOption (opt : @& String) : Bool

@[extern "lean_cadical_solver_is_valid_long_option"]
public opaque isValidLongOption (opt : @& String) : Bool

@[extern "lean_cadical_solver_get"]
public opaque get (s : @& Solver) (opt : @& String) : BaseIO Int32

@[extern "lean_cadical_solver_set"]
public opaque set (s : @& Solver) (opt : @& String) (val : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_set_long_option"]
public opaque setLongOption (s : @& Solver) (opt : @& String) : BaseIO Bool

@[extern "lean_cadical_solver_is_valid_configuration"]
public opaque isValidConfiguration (opt : @& String) : Bool

@[extern "lean_cadical_solver_configure"]
public opaque configure (s : @& Solver) (opt : @& String) : BaseIO Bool

@[extern "lean_cadical_solver_optimize"]
public opaque optimize (s : @& Solver) (val : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_limit"]
public opaque limit (s : @& Solver) (limit : @& String) (val : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_is_valid_limit"]
public opaque isValidLimit (s : @& Solver) (limit : @& String) : BaseIO Bool

@[extern "lean_cadical_solver_active"]
public opaque active (s : @& Solver) : BaseIO Int32

@[extern "lean_cadical_solver_redundant"]
public opaque redundant (s : @& Solver) : BaseIO Int64

@[extern "lean_cadical_solver_irredundant"]
public opaque irredundant (s : @& Solver) : BaseIO Int64

@[extern "lean_cadical_solver_simplify"]
public opaque simplify (s : @& Solver) (rounds : Int32) : BaseIO Status

@[extern "lean_cadical_solver_terminate"]
public opaque terminate (s : @& Solver) : BaseIO Unit

@[extern "lean_cadical_solver_frozen"]
public opaque frozen (s : @& Solver) (lit : Int32) : BaseIO Bool

@[extern "lean_cadical_solver_freeze"]
public opaque freeze (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_melt"]
public opaque melt (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_fixed"]
public opaque fixed (s : @& Solver) (lit : Int32) : BaseIO Int32

@[extern "lean_cadical_solver_phase"]
public opaque phase (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_unphase"]
public opaque unphase (s : @& Solver) (lit : Int32) : BaseIO Unit

@[extern "lean_cadical_solver_conclude"]
public opaque conclude (s : @& Solver) : BaseIO Unit

@[extern "lean_cadical_solver_usage"]
public opaque usage : IO Unit

@[extern "lean_cadical_solver_configurations"]
public opaque configurations : IO Unit

@[extern "lean_cadical_solver_statistics"]
public opaque statistics (s : @& Solver) : IO Unit

@[extern "lean_cadical_solver_resources"]
public opaque resources (s : @& Solver) : IO Unit

@[extern "lean_cadical_solver_state"]
public opaque state (s : @& Solver) : BaseIO UInt16

/-
TODO for the future:
- proof trace
- terminators
-/

end Solver

end Lean.Cadical.Internal
