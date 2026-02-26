set_option cbv.warning false

-- Success: proposition reduces to `Bool.true`
example : 1 + 1 = 2 := by decide_cbv

example : 1 ∈ [1, 2, 3] := by decide_cbv

/-- error: `decide_cbv` failed: the proposition evaluates to `false` -/
#guard_msgs (error) in
example : 1 + 1 = 3 := by decide_cbv

opaque myOpaqueBool : Bool

/--
error: `decide_cbv` failed: could not reduce the expression to a boolean value; got stuck at: ⏎
  Decidable.rec (fun h => false) (fun h => true)
    (match myOpaqueBool, true with
    | false, false => isTrue ⋯
    | false, true => isFalse ⋯
    | true, false => isFalse ⋯
    | true, true => isTrue ⋯)
-/
#guard_msgs (error) in
example : myOpaqueBool = true := by decide_cbv
