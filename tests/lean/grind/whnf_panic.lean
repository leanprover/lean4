namespace List

-- This should report an invalid pattern, but should not panic.
theorem countP_filterMap' {p : β → Bool} {f : α → Option β} {l : List α} :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  induction l with grind [=_ Option.getD_map]-- TODO
