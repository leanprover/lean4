/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.AppBuilder
namespace Lean.Meta.Sym.Simp

/-!
# Dischargers for Conditional Rewrite Rules

This module provides dischargers for handling conditional rewrite rules in `Sym.simp`.
A discharger attempts to prove side conditions that arise during rewriting.

## Overview

When applying a conditional rewrite rule `h : P → a = b`, the simplifier must prove
the precondition `P` before using the rule. A `Discharger` is a function that attempts
to construct such proofs.

**Example**: Consider the rewrite rule:
```
theorem div_self (n : Nat) (h : n ≠ 0) : n / n = 1
```
When simplifying `x / x`, the discharger must prove `x ≠ 0` to apply this rule.

## Design

Dischargers work by:
1. Attempting to simplify the side condition to `True`
2. If successful, extracting a proof from the simplification result
3. Returning `.failed` if the condition cannot be discharged

Each discharge result also carries a `contextDependent` flag indicating whether
the discharge used context-dependent information (e.g., local hypotheses).
This enables the simplifier's two-tier cache to correctly handle context-dependent results.
-/

/-- Result of a discharge attempt. -/
public inductive DischargeResult where
  /-- Discharge failed. If `contextDependent = true`, it might succeed in another local context. -/
  | failed (contextDependent : Bool := false)
  /-- Discharge succeeded with the given proof. -/
  | solved (proof : Expr) (contextDependent : Bool := false)

/--
A discharger attempts to prove propositions that arise as side conditions during rewriting.

Given a proposition `e : Prop`, returns:
- `.solved proof` if `e` can be proven
- `.failed` otherwise

Both carry a `contextDependent` flag indicating whether context-dependent
information was used during the attempt.
-/
public abbrev Discharger := Expr → SimpM DischargeResult

def resultToDischargeResult (e : Expr) (result : Result) : DischargeResult :=
  match result with
  | .rfl _ cd => .failed cd
  | .step e' h _ cd =>
    if e'.isTrue then
      .solved (mkOfEqTrueCore e h) cd
    else
      .failed cd

/--
Converts a simplification procedure into a discharger.

A `Simproc` can be used as a discharger by simplifying the side condition and
checking if it reduces to `True`. If so, the equality proof is converted to
a proof of the original proposition.

**Algorithm**:
1. Apply the simproc to the side condition `e`
2. If `e` simplifies to `True` (via proof `h : e = True`), return `ofEqTrue h : e`
3. Otherwise, return `.failed` (cannot discharge)

**Parameters**:
- `p`: A simplification procedure to use for discharging conditions

**Example**: If `p` simplifies `5 < 10` to `True` via proof `h : (5 < 10) = True`,
then `mkDischargerFromSimproc p` returns `ofEqTrue h : 5 < 10`.
-/
public def mkDischargerFromSimproc (p : Simproc) : Discharger := fun e => do
  return resultToDischargeResult e (← p e)

/--
The default discharger uses the simplifier itself to discharge side conditions.

This creates a natural recursive behavior: when applying conditional rules,
the simplifier is invoked to prove their preconditions. This is effective because:

1. **Ground terms**: Conditions like `5 ≠ 0` are evaluated by simprocs
2. **Recursive simplification**: Complex conditions are reduced to simpler ones
3. **Lemma application**: The simplifier can apply other rewrite rules to conditions

It ensures the cached results are discarded, and increases the discharge depth to avoid
infinite recursion.
-/
public def dischargeSimpSelf : Discharger := fun e => do
  if (← readThe Context).dischargeDepth > (← getConfig).maxDischargeDepth then
    return .failed
  withoutModifyingCache do
  withTheReader Context (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
    return resultToDischargeResult e (← simp e)

/--
A discharger that fails to prove any side condition.

This is used when conditional rewrite rules should not be applied. It immediately
returns `.failed` for all propositions, effectively disabling conditional rewriting.

**Use cases**:
- Testing: Isolating unconditional rewriting behavior
- Performance: Avoiding expensive discharge attempts when conditions are unlikely to hold
- Controlled rewriting: Explicitly disabling conditional rules in specific contexts
-/
public def dischargeNone : Discharger := fun _ =>
  return .failed

/--
A discharger for testing that proves side conditions using hypotheses from the
local context. Always context-dependent: available hypotheses change when entering binders.
-/
public def dischargeAssumption : Discharger := fun e => do
  for localDecl in (← getLCtx) do
    if localDecl.isAuxDecl then continue
    if (← isDefEq localDecl.type e) then
      return .solved localDecl.toExpr true
  return .failed true

end Lean.Meta.Sym.Simp
