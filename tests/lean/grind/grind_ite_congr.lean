set_option grind.warning false

example : ((if true then id else id) false) = false := by
  grind

example : ((if (!false) = true then id else id) false) = false := by
  decide

example : ((if (!false) = true then id else id) false) = false := by
  grind -- fails
