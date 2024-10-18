/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.LRAT
import Lean.Elab.Tactic.BVDecide.External
import Lean.Elab.Tactic.BVDecide.Frontend

/-!
This directory offers three different SAT tactics for proving goals involving `BitVec` and `Bool`:
1. `bv_decide` takes the goal, hands it over to a SAT solver and verifies the generated LRAT
   UNSAT proof to prove the goal.
2. `bv_check file.lrat` can prove the same things as `bv_decide`. However instead of
   dynamically handing the goal to a SAT solver to obtain an LRAT proof, the LRAT proof is read from
   `file.lrat`. This allows users that do not have a SAT solver installed to verify proofs.
3. `bv_decide?` offers a code action to turn a `bv_decide` invocation automatically into a
   `bv_check` one.

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
3. Use proof by reflection to reduce the proof to showing that an SMTLIB-syntax-like value that
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
`bv_decide` makes use of proof by reflection and `ofReduceBool`, thus adding the Lean compiler to
the trusted code base.


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
6. Add the reflection code to `Lean.Elab.Tactic.BVDecide.Frontend.BVDecide`
7. Add a test!
-/
