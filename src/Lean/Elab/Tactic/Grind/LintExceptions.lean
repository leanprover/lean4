/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Lint

-- We allow these as grind lemmas even though they triggers >20 further instantiations.
-- See tests/lean/run/grind_lint_*.lean for more details.
#grind_lint skip BitVec.msb_replicate
#grind_lint skip BitVec.msb_signExtend
#grind_lint skip List.replicate_sublist_iff
#grind_lint skip List.Sublist.append
#grind_lint skip List.Sublist.middle
#grind_lint skip List.getLast?_pmap
#grind_lint skip Array.count_singleton
#grind_lint skip Array.foldl_empty
#grind_lint skip Array.foldr_empty

#grind_lint skip suffix sizeOf_spec
