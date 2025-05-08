-- Prior to https://github.com/leanprover/lean4/pull/8230
-- this  failing silently (but not adding `g` to the environment).

#guard_msgs (drop info) in
partial def g :
  have : False := by apply?
  False := g
