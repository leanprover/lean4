import Std
import Lean.Elab.Tactic.Grind.LintExceptions

/-! Check Array namespace: -/

-- These go slightly over 20, but seem reasonable.
#guard_msgs in
#grind_lint inspect (min := 22) Array.count_singleton
#guard_msgs in
#grind_lint inspect (min := 22) Array.foldl_empty
#guard_msgs in
#grind_lint inspect (min := 22) Array.foldr_empty

-- `Array.back_singleton` is reasonable at 23.
#guard_msgs in
#grind_lint inspect (min := 25) Array.back_singleton

-- `Array.getElem_zero_filter` is reasonable at 20.
#guard_msgs in
#grind_lint inspect (min := 22) Array.getElem_zero_filter

-- `Array.getElem_zero_filterMap` is reasonable at 20.
#guard_msgs in
#grind_lint inspect (min := 22) Array.getElem_zero_filterMap

-- TODO: Is `Array.drop_append_size` reasonable at 35?
-- This seems to be worse than `List.drop_append_length` because
-- `#[]` is actually `[].toArray`, triggering more instantiations.
#guard_msgs in
#grind_lint inspect  (min := 35)Array.drop_append_size

#guard_msgs in
#grind_lint check (min := 20) in Array
