/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module  -- shake: keep-all (almost-terminal module, `#grind_lint` does not track extra deps)
prelude
import Init
import Std
import Lean.Elab.Tactic.Grind.Lint

-- We allow these as grind lemmas even though they triggers >20 further instantiations.
-- See tests/lean/run/grind_lint_*.lean for more details.
#grind_lint skip BitVec.msb_replicate
#grind_lint skip BitVec.msb_signExtend
#grind_lint skip List.replicate_sublist_iff
#grind_lint skip List.Sublist.append
#grind_lint skip List.Sublist.middle
#grind_lint skip List.getLast?_pmap
#grind_lint skip List.getLast_attach
#grind_lint skip List.getLast_attachWith
#grind_lint skip List.head_attachWith
#grind_lint skip List.drop_append_length
#grind_lint skip Array.back_singleton
#grind_lint skip Array.count_singleton
#grind_lint skip Array.foldl_empty
#grind_lint skip Array.foldr_empty
#grind_lint skip Array.getElem_zero_filter
#grind_lint skip Array.getElem_zero_filterMap
#grind_lint skip Std.ExtHashMap.getElem_filterMap'
#grind_lint skip Std.ExtTreeMap.getElem_filterMap'
#grind_lint skip Std.HashMap.getElem_filterMap'
#grind_lint skip Std.TreeMap.getElem_filterMap'

#grind_lint skip suffix sizeOf_spec
