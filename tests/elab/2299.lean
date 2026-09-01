class Abs (α : Type _) where
  abs : α → α

macro:max atomic("|" noWs) a:term noWs "|" : term => `(Abs.abs $a)

-- check that `|-` is not parsed as a single token.
example [Abs α] [Neg α] (n : α) : |-n| = |-n| := rfl
