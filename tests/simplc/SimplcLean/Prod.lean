import SimplcLean._root_

simp_lc ignore Prod.exists
simp_lc ignore Prod.forall

#guard_msgs (drop info) in
simp_lc check in Prod _root_
