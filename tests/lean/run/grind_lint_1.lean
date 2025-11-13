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

/-- info: instantiating `Array.range_succ` triggers 47 additional `grind` theorem instantiations -/
#guard_msgs in
#grind_lint inspect Array.range_succ

#grind_lint inspect (min := 100) Array.range_succ

#grind_lint mute Array.append_assoc -- It is not used during E-matching by `#grind_lint check` and `#grind_lint inspect`

/-- info: instantiating `Array.range_succ` triggers 22 additional `grind` theorem instantiations -/
#guard_msgs in
#grind_lint inspect Array.range_succ

/--
info: instantiating `Array.range_succ` triggers 22 additional `grind` theorem instantiations
---
info: instantiating `Array.range'_succ` triggers 17 additional `grind` theorem instantiations
-/
#guard_msgs in
#grind_lint inspect Array.range_succ Array.range'_succ

/--
info: instantiating `Array.extract_empty` triggers more than 100 additional `grind` theorem instantiations
---
info: instantiating `Array.filterMap_some` triggers more than 100 additional `grind` theorem instantiations
---
info: instantiating `Array.range_succ` triggers 22 additional `grind` theorem instantiations
-/
#guard_msgs in
#grind_lint check (min := 20) (detailed := 200) in Array

#grind_lint skip Array.extract_empty -- `#grind_lint check` skips it from now on

/--
info: instantiating `Array.filterMap_some` triggers more than 100 additional `grind` theorem instantiations
---
info: instantiating `Array.range_succ` triggers 22 additional `grind` theorem instantiations
-/
#guard_msgs in
#grind_lint check (min := 20) (detailed := 200) in Array

/--
info: instantiating `Array.filterMap_some` triggers more than 100 additional `grind` theorem instantiations
---
info: Array.filterMap_some
[thm] instances
  [thm] Array.filterMap_filterMap ↦ 94
  [thm] Array.size_filterMap_le ↦ 5
  [thm] Array.filterMap_some ↦ 1
-/
#guard_msgs in
#grind_lint inspect Array.filterMap_some
