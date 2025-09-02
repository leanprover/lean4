/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Attr
public import Lean.Meta.Tactic.Grind.RevertAll
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Util
public import Lean.Meta.Tactic.Grind.Cases
public import Lean.Meta.Tactic.Grind.Injection
public import Lean.Meta.Tactic.Grind.Core
public import Lean.Meta.Tactic.Grind.Canon
public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
public import Lean.Meta.Tactic.Grind.Inv
public import Lean.Meta.Tactic.Grind.Proof
public import Lean.Meta.Tactic.Grind.Propagate
public import Lean.Meta.Tactic.Grind.PP
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.Ctor
public import Lean.Meta.Tactic.Grind.Parser
public import Lean.Meta.Tactic.Grind.EMatchTheorem
public import Lean.Meta.Tactic.Grind.EMatch
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.Grind.CasesMatch
public import Lean.Meta.Tactic.Grind.Arith
public import Lean.Meta.Tactic.Grind.Ext
public import Lean.Meta.Tactic.Grind.MatchCond
public import Lean.Meta.Tactic.Grind.MatchDiscrOnly
public import Lean.Meta.Tactic.Grind.Diseq
public import Lean.Meta.Tactic.Grind.MBTC
public import Lean.Meta.Tactic.Grind.Lookahead
public import Lean.Meta.Tactic.Grind.LawfulEqCmp
public import Lean.Meta.Tactic.Grind.ReflCmp
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.AC
public import Lean.Meta.Tactic.Grind.VarRename
public import Lean.Meta.Tactic.Grind.ProofUtil

public section

namespace Lean

/-! Trace options for `grind` users -/
builtin_initialize registerTraceClass `grind
builtin_initialize registerTraceClass `grind.trace
builtin_initialize registerTraceClass `grind.assert
builtin_initialize registerTraceClass `grind.eqc
builtin_initialize registerTraceClass `grind.internalize
builtin_initialize registerTraceClass `grind.ematch
builtin_initialize registerTraceClass `grind.ematch.pattern
builtin_initialize registerTraceClass `grind.ematch.instance
builtin_initialize registerTraceClass `grind.ematch.instance.assignment
builtin_initialize registerTraceClass `grind.eqResolution
builtin_initialize registerTraceClass `grind.issues
builtin_initialize registerTraceClass `grind.simp
builtin_initialize registerTraceClass `grind.split
builtin_initialize registerTraceClass `grind.split.candidate
builtin_initialize registerTraceClass `grind.split.resolved
builtin_initialize registerTraceClass `grind.beta
builtin_initialize registerTraceClass `grind.mbtc
builtin_initialize registerTraceClass `grind.ext
builtin_initialize registerTraceClass `grind.ext.candidate
builtin_initialize registerTraceClass `grind.lookahead
builtin_initialize registerTraceClass `grind.lookahead.add (inherited := true)
builtin_initialize registerTraceClass `grind.lookahead.try (inherited := true)
builtin_initialize registerTraceClass `grind.lookahead.assert (inherited := true)

/-! Trace options for `grind` developers -/
builtin_initialize registerTraceClass `grind.debug
builtin_initialize registerTraceClass `grind.debug.proofs
builtin_initialize registerTraceClass `grind.debug.congr
builtin_initialize registerTraceClass `grind.debug.proof
builtin_initialize registerTraceClass `grind.debug.proj
builtin_initialize registerTraceClass `grind.debug.parent
builtin_initialize registerTraceClass `grind.debug.final
builtin_initialize registerTraceClass `grind.debug.forallPropagator
builtin_initialize registerTraceClass `grind.debug.split
builtin_initialize registerTraceClass `grind.debug.canon
builtin_initialize registerTraceClass `grind.debug.ematch.activate
builtin_initialize registerTraceClass `grind.debug.ematch.pattern
builtin_initialize registerTraceClass `grind.debug.beta
builtin_initialize registerTraceClass `grind.debug.internalize
builtin_initialize registerTraceClass `grind.debug.matchCond
builtin_initialize registerTraceClass `grind.debug.matchCond.lambda
builtin_initialize registerTraceClass `grind.debug.matchCond.proveFalse
builtin_initialize registerTraceClass `grind.debug.mbtc
builtin_initialize registerTraceClass `grind.debug.ematch
builtin_initialize registerTraceClass `grind.debug.proveEq
builtin_initialize registerTraceClass `grind.debug.pushNewFact
builtin_initialize registerTraceClass `grind.debug.appMap
builtin_initialize registerTraceClass `grind.debug.ext

end Lean
