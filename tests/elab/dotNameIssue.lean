example : x ≠ y → x ∉ [y] :=
  fun hne hin =>
    match hin with
    | .head _ => hne rfl

example : x ≠ y → x ∉ [y] :=
  fun hne (.head _) => hne rfl
