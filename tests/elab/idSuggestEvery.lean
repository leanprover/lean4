-- test every/all replacements in default imports

/-
Expected replacements for `Subarray.any` and `Subarray.all` do not work as suggestion annotations
when using generalized field notation: Subarray is an abbreviation and so the underlying `Std.Slice`
type, which does not have a corresponding `.any`/`.all` function.
-/

/--
error: Invalid field `every`: The environment does not contain `Std.Slice.every`, so it is not possible to project the field `every` from an expression
  x
of type
  Std.Slice (Std.Slice.Internal.SubarrayData Nat)
-/
#guard_msgs in example (x : Subarray Nat) := x.every fun _ => true
#guard_msgs in example (x : Subarray Nat) := x.all fun _ => true

/--
error: Unknown constant `Subarray.every`

Hint: Perhaps you meant `Subarray.all` in place of `Subarray.every`:
  [apply] `Subarray.all`
-/
#guard_msgs in example := (@Subarray.every Nat (fun _ => true) ·)
#guard_msgs in example := (@Subarray.all Nat (fun _ => true) ·)

/--
error: Unknown constant `Subarray.some`

Hint: Perhaps you meant `Subarray.any` in place of `Subarray.some`:
  [apply] `Subarray.any`
-/
#guard_msgs in example := (@Subarray.some Nat (fun _ => true) ·)
#guard_msgs in example := (@Subarray.any Nat (fun _ => true) ·)

/--
error: Invalid field `every`: The environment does not contain `String.every`, so it is not possible to project the field `every` from an expression
  x
of type `String`

Hint: Perhaps you meant `String.all` in place of `String.every`:
  .e̵v̵e̵r̵y̵a̲l̲l̲
-/
#guard_msgs in example (x : String) := x.every fun _ => true
#guard_msgs in example (x : String) := x.all fun _ => true
/--
error: Invalid field `some`: The environment does not contain `String.some`, so it is not possible to project the field `some` from an expression
  x
of type `String`

Hint: Perhaps you meant `String.contains` in place of `String.some`:
  .s̵o̵m̵e̵c̲o̲n̲t̲a̲i̲n̲s̲
-/
#guard_msgs in example (x : String) := x.some fun _ => true
#guard_msgs in example (x : String) := x.contains fun _ => true


/--
error: Invalid field `every`: The environment does not contain `Array.every`, so it is not possible to project the field `every` from an expression
  x
of type `Array Nat`

Hint: Perhaps you meant `Array.all` in place of `Array.every`:
  .e̵v̵e̵r̵y̵a̲l̲l̲
-/
#guard_msgs in example (x : Array Nat) := x.every fun _ => true
#guard_msgs in example (x : Array Nat) := x.all fun _ => true
/--
error: Invalid field `some`: The environment does not contain `Array.some`, so it is not possible to project the field `some` from an expression
  x
of type `Array Nat`

Hint: Perhaps you meant `Array.any` in place of `Array.some`:
  .s̵o̵m̵e̵a̲n̲y̲
-/
#guard_msgs in example (x : Array Nat) := x.some fun _ => true
#guard_msgs in example (x : Array Nat) := x.all fun _ => true

/--
error: Invalid field `every`: The environment does not contain `List.every`, so it is not possible to project the field `every` from an expression
  x
of type `List Nat`

Hint: Perhaps you meant `List.all` in place of `List.every`:
  .e̵v̵e̵r̵y̵a̲l̲l̲
-/
#guard_msgs in example (x : List Nat) := x.every fun _ => true
#guard_msgs in example (x : List Nat) := x.all fun _ => true
/--
error: Invalid field `some`: The environment does not contain `List.some`, so it is not possible to project the field `some` from an expression
  x
of type `List Nat`

Hint: Perhaps you meant `List.any` in place of `List.some`:
  .s̵o̵m̵e̵a̲n̲y̲
-/
#guard_msgs in example (x : List Nat) := x.some fun _ => true
#guard_msgs in example (x : List Nat) := x.all fun _ => true

/--
@ +1:17...22
error: Invalid field `every`: The environment does not contain `List.every`, so it is not possible to project the field `every` from an expression
  [1, 2, 3]
of type `List ?m.10`

Hint: Perhaps you meant `List.all` in place of `List.every`:
  .e̵v̵e̵r̵y̵a̲l̲l̲
-/
#guard_msgs (positions := true) in
#check [1, 2, 3].every
