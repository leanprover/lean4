/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Notation
import Init.Simproc

set_option linter.missingDocs true -- keep it documented

namespace Lean.Parser

namespace Tactic

/--
This tactic works just like `bv_decide` but skips calling a SAT solver by using a proof that is
already stored on disk. It is called with the name of an LRAT file in the same directory as the
current Lean file:
```
bv_check "proof.lrat"
```
-/
syntax (name := bvCheck) "bv_check " str : tactic

/--
Close fixed-width `BitVec` and `Bool` goals by obtaining a proof from an external SAT solver and
verifying it inside Lean. The solvable goals are currently limited to the Lean equivalent of
[`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV):
```lean
example : ∀ (a b : BitVec 64), (a &&& b) + (a ^^^ b) = a ||| b := by
  intros
  bv_decide
```

If `bv_decide` encounters an unknown definition it will be treated like an unconstrained `BitVec`
variable. Sometimes this enables solving goals despite not understanding the definition because
the precise properties of the definition do not matter in the specific proof.

If `bv_decide` fails to close a goal it provides a counter-example, containing assignments for all
terms that were considered as variables.

In order to avoid calling a SAT solver every time, the proof can be cached with `bv_decide?`.

If solving your problem relies inherently on using associativity or commutativity, consider enabling
the `bv.ac_nf` option.


Note: `bv_decide` uses `ofReduceBool` and thus trusts the correctness of the code generator.
-/
syntax (name := bvDecide) "bv_decide" : tactic


/--
Suggest a proof script for a `bv_decide` tactic call. Useful for caching LRAT proofs.
-/
syntax (name := bvTrace) "bv_decide?" : tactic

/--
Run the normalization procedure of `bv_decide` only. Sometimes this is enough to solve basic
`BitVec` goals already.
-/
syntax (name := bvNormalize) "bv_normalize" : tactic

end Tactic

/--
Auxiliary attribute for builtin `bv_normalize` simprocs.
-/
syntax (name := bvNormalizeProcBuiltinAttr) "builtin_bv_normalize_proc" (Tactic.simpPre <|> Tactic.simpPost)? : attr

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind builtin_simproc $[$pre?]? [bv_normalize] $n:ident ($pattern:term) := $body) => do
    `($[$doc?:docComment]? builtin_simproc_decl $n ($pattern) := $body
      attribute [$kind builtin_bv_normalize_proc $[$pre?]?] $n)

end Lean.Parser
