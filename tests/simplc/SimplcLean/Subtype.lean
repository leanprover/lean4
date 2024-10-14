import SimplcLean._root_

simp_lc ignore Subtype.exists
simp_lc ignore Subtype.forall

#guard_msgs (drop info) in
simp_lc check in Subtype _root_
