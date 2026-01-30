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
3. Returning `none` if the condition cannot be discharged

This integrates naturally with `Simproc`-based simplification.

## Important

When using dischargers that access new local declarations introduced when
visiting binders, it is the user's responsibility to set `wellBehavedMethods := false`.
This setting will instruct `simp` to discard the cache after visiting the binder's body.
-/

/--
A discharger attempts to prove propositions that arise as side conditions during rewriting.

Given a proposition `e : Prop`, returns:
- `some proof` if `e` can be proven
- `none` if `e` cannot be discharged

**Usage**: Dischargers are used by the simplifier when applying conditional rewrite rules.
-/
public abbrev Discharger := Expr → SimpM (Option Expr)

def resultToOptionProof (e : Expr) (result : Result) : Option Expr :=
  match result with
  | .rfl _ => none
  | .step e' h _ =>
    if e'.isTrue then
      some <| mkOfEqTrueCore e h
    else
      none

/--
Converts a simplification procedure into a discharger.

A `Simproc` can be used as a discharger by simplifying the side condition and
checking if it reduces to `True`. If so, the equality proof is converted to
a proof of the original proposition.

**Algorithm**:
1. Apply the simproc to the side condition `e`
2. If `e` simplifies to `True` (via proof `h : e = True`), return `ofEqTrue h : e`
3. Otherwise, return `none` (cannot discharge)

**Parameters**:
- `p`: A simplification procedure to use for discharging conditions

**Example**: If `p` simplifies `5 < 10` to `True` via proof `h : (5 < 10) = True`,
then `mkDischargerFromSimproc p` returns `ofEqTrue h : 5 < 10`.
-/
public def mkDischargerFromSimproc (p : Simproc) : Discharger := fun e => do
  return resultToOptionProof e (← p e)

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
    return none
  withoutModifyingCache do
  withTheReader Context (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
    return resultToOptionProof e (← simp e)

/--
A discharger that fails to prove any side condition.

This is used when conditional rewrite rules should not be applied. It immediately
returns `none` for all propositions, effectively disabling conditional rewriting.

**Use cases**:
- Testing: Isolating unconditional rewriting behavior
- Performance: Avoiding expensive discharge attempts when conditions are unlikely to hold
- Controlled rewriting: Explicitly disabling conditional rules in specific contexts
-/
public def dischargeNone : Discharger := fun _ =>
  return none

end Lean.Meta.Sym.Simp
