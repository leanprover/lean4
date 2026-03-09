syntax blockingConsts := "blocking" "[" ident,* "]"
macro "specialize_def" i:ident "[" ts:term,* "]" block:blockingConsts : tactic => do
  /- expected 'blocking' -/
  if let `(blockingConsts|blocking [ $is:ident,* ]) := block then
    sorry
  sorry
