def List.eq [BEq α] (xs ys : List α) : Bool :=
  if _ : xs.ctorIdx != ys.ctorIdx then
    false
  else
    match xs, ys with
    | nil, nil => true
    | cons x xs, cons y ys => x == y && xs.eq ys


example : List.eq ([] : List Bool) [] = true := rfl

/--
error: Type mismatch
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  [true].eq [] = false
-/
#guard_msgs in
example : List.eq ([true] : List Bool) [] = false := rfl

set_option smartUnfolding false in
example : List.eq ([true] : List Bool) [] = false := rfl

/--
info: def List.eq._sunfold.{u_1} : {α : Type u_1} → [BEq α] → List α → List α → Bool :=
fun {α} [BEq α] xs ys =>
  if x : (xs.ctorIdx != ys.ctorIdx) = true then false
  else
    match xs, ys, x with
    | [], [], x => true
    | x :: xs, y :: ys, x_1 => x == y && xs.eq ys
-/
#guard_msgs in
#print List.eq._sunfold
