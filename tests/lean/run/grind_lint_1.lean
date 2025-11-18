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

#guard_msgs in
#grind_lint check (min := 20) in Array

#grind_lint skip Array.extract_empty -- `#grind_lint check` skips it from now on

#guard_msgs in
#grind_lint check (min := 20) in Array

#guard_msgs in
#grind_lint inspect Array.filterMap_some

#guard_msgs in
#grind_lint check (min := 20) in module Init.Data.Array
