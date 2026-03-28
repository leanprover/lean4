module
example : ((if true then id else id) false) = false := by
  grind

example : ((if (!false) = true then id else id) false) = false := by
  decide

example : ((if (!false) = true then id else id) false) = false := by
  grind -- must not fail
