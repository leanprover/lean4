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

/-- info: Array.range_succ : 47 -/
#guard_msgs in
#grind_lint inspect Array.range_succ

#grind_lint inspect (min := 100) Array.range_succ

#grind_lint mute Array.append_assoc -- Reduces the number of instantiations in the following command

/-- info: Array.range_succ : 22 -/
#guard_msgs in
#grind_lint inspect Array.range_succ

/--
info: Array.range_succ : 22
---
info: Array.range'_succ : 17
-/
#guard_msgs in
#grind_lint inspect Array.range_succ Array.range'_succ

/--
info: Array.extract_empty : 100
---
info: Array.filterMap_some : 100
---
info: Array.range_succ : 22
-/
#guard_msgs in
#grind_lint check (min := 20) (detailed := 200) in Array
