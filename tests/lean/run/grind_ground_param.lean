opaque π : Rat
axiom pi_pos : 0 < π

example : π = 0 → False := by
  grind [pi_pos]

example : 0 < 2 * π := by
  grind [pi_pos]
