#grind_lint mute Array.getElem_swap

/--
error: `Array.swap_swap` is not marked with the `@[grind]` attribute for theorem instantiation
-/
#guard_msgs in
#grind_lint mute Array.swap_swap

/-- error: `Array.getElem_swap` is already in the `#grind_lint` mute set -/
#guard_msgs in
#grind_lint mute Array.getElem_swap

#grind_lint skip Array.getElem_swap

/--
error: `Array.swap_swap` is not marked with the `@[grind]` attribute for theorem instantiation
-/
#guard_msgs in
#grind_lint skip Array.swap_swap

/-- error: `Array.getElem_swap` is already in the `#grind_lint` skip set -/
#guard_msgs in
#grind_lint skip Array.getElem_swap

/--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ
-/
#guard_msgs in
#grind_lint inspect Array.range_succ

#grind_lint inspect (min := 100) Array.range_succ

#grind_lint mute Array.append_assoc -- It is not used during E-matching by `#grind_lint check` and `#grind_lint inspect`

/--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ
-/
#guard_msgs in
#grind_lint inspect Array.range_succ

/--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: instantiating `Array.range'_succ` triggers 14 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ Array.range'_succ
-/
#guard_msgs in
#grind_lint inspect Array.range_succ Array.range'_succ

-- These go slightly over 20, but seem reasonable.
#grind_lint skip Array.count_singleton
#grind_lint skip Array.foldl_empty
#grind_lint skip Array.foldr_empty

#guard_msgs in
#grind_lint check (min := 20) in Array

#guard_msgs in
#grind_lint inspect Array.filterMap_some

#guard_msgs in
#grind_lint check (min := 20) in module Init.Data.Array

/-! Test suffix skipping -/

#grind_lint skip suffix succ

/-- error: `succ` is already in the `#grind_lint` skip suffix set -/
#guard_msgs in
#grind_lint skip suffix succ

-- First, let's verify individual theorems ending in succ would normally trigger warnings
-- This should show that Array.range_succ triggers instantiations
/--
info: instantiating `Array.range_succ` triggers 19 additional `grind` theorem instantiations
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect Array.range_succ
-/
#guard_msgs in
#grind_lint inspect Array.range_succ

-- Now verify that theorems ending in `succ` are skipped in check
-- Note: The suffix skip should apply during check, but inspect bypasses it
-- Array.range_succ and Array.range'_succ should NOT appear in the output
/--
info: instantiating `Array.back?_empty` triggers 17 additional `grind` theorem instantiations
---
info: instantiating `Array.count_empty` triggers 19 additional `grind` theorem instantiations
---
info: instantiating `Array.findIdx_empty` triggers 20 additional `grind` theorem instantiations
---
info: instantiating `Array.findIdx_singleton` triggers 16 additional `grind` theorem instantiations
---
info: Try this:
  [apply] #grind_lint check  (min := 15) in Array
  #grind_lint inspect Array.back?_empty
  #grind_lint inspect Array.count_empty
  #grind_lint inspect Array.findIdx_empty
  #grind_lint inspect Array.findIdx_singleton
-/
#guard_msgs in
#grind_lint check (min := 15) in Array
