import SimplcLean._root_

-- These are facts about `Array Prop`, which hopefully never appear in the wild!
simp_lc whitelist dite_else_false Array.getD_eq_get?
simp_lc whitelist dite_else_true Array.getD_eq_get?

-- TODO: fixable, with a more general `Array.foldr_push'` simp lemma.
simp_lc whitelist Array.foldr_push' Array.foldr_subtype'

-- TODO: move to library
@[simp] theorem List.mapM_id {l : List α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l <;> simp_all

-- TODO: move to library
@[simp] theorem Array.mapM_id {l : Array α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l <;> simp_all

#guard_msgs (drop info) in
simp_lc check in Array Id _root_
