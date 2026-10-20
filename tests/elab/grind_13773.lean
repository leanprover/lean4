/-! https://github.com/leanprover/lean4/issues/13773

`grind` was building proofs of `Grind.MatchCond` using the grind goal as the
`mkNoConfusion` target, which produced terms whose type appended the goal's
binders after the `MatchCond` body and was rejected by the kernel. -/

theorem ex
    (a b : Bool)
    (h : match a, b with
      | false, false => True
      | true, true => True
      | _, _ => False) :
    match a, b with
    | false, false => True
    | true, true => True
    | _, _ => False := by
  grind

theorem ex2
    (p : Prop)
    (a b : Bool)
    (h : match a, b with
      | false, false => True
      | true, true => p
      | _, _ => False) :
    match a, b with
    | false, false => True
    | true, true => p
    | _, _ => False := by
  grind
