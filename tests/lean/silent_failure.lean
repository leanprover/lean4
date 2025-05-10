-- This was previously failing silently (but not adding `g` to the environment).

#guard_msgs (drop info) in
partial def g :
  have : False := by apply?
  False := g
