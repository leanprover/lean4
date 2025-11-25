open List

example (h : zs <+ ys) (w : xs ++ ys <+ zs) (h' : ¬xs = []) : False := by
  fail_if_success grind
  -- I'm not sure how to make progress here without manually adding that since `xs ≠ []`, it must be a `cons`.
  have : ∃ y ys, xs = y :: ys := match xs, h' with | _ :: _, _ => by simp
  grind (gen := 6)

example {xs ys zs : List α} (h : zs <+ ys) :
    xs ++ ys <+ zs ↔ xs = [] ∧ ys = zs := by
  constructor
  · intro w
    grind -- stuck, because of the failure of the example above.
    -- An alternative idea would be to argue via inequalities about lengths,
    -- but any grind pattern for `Sublist.length_le` seems to result in an explosion of useless facts.
  · intro w
    grind
