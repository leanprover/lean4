-- Already working:

-- #grind_lint check (min := 20) in Array

-- In progress:

#grind_lint check  (min := 20) in List
#grind_lint inspect List.getLast?_concat
#grind_lint inspect List.getLast?_pmap
#grind_lint inspect List.getLast_filter
#grind_lint inspect List.head_filter
#grind_lint inspect List.length_modifyTailIdx
#grind_lint inspect List.replicate_sublist_iff
#grind_lint inspect List.reverse_concat
#grind_lint inspect List.reverse_flatMap
#grind_lint inspect List.Sublist.append
#grind_lint inspect List.Sublist.middle


/--
info: instantiating `Vector.extract_reverse` triggers 22 additional `grind` theorem instantiations
---
info: instantiating `Vector.range'_one` triggers more than 100 additional `grind` theorem instantiations
---
info: Vector.range'_one
[thm] instances
  [thm] Vector.append_assoc ↦ 29
  [thm] Vector.range'_append ↦ 15
  [thm] Vector.append_assoc_symm ↦ 12
  [thm] Vector.empty_append ↦ 11
  [thm] List.size_toArray ↦ 8
  [thm] Vector.range'_one ↦ 8
  [thm] Vector.range'_zero ↦ 7
  [thm] List.length_cons ↦ 6
  [thm] Array.size_empty ↦ 1
  [thm] List.length_nil ↦ 1
  [thm] Vector.append_empty ↦ 1
  [thm] Vector.toArray_empty ↦ 1
---
info: instantiating `Vector.reverse_extract` triggers 22 additional `grind` theorem instantiations
---
info: Try this:
  [apply] #grind_lint check  (min := 20) in Vector
  #grind_lint inspect Vector.extract_reverse
  #grind_lint inspect Vector.range'_one
  #grind_lint inspect Vector.reverse_extract
-/
#guard_msgs in
#grind_lint check (min := 20) in Vector

-- TODO:

-- #grind_lint check (min := 20) in Option
-- #grind_lint check (min := 20) in Nat Int Rat Dyadic
-- #grind_lint check (min := 20) in Prod Sum
-- #grind_lint check (min := 20) in module Std
-- #grind_lint check (min := 20)
