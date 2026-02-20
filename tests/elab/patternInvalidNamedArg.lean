/-!
# Invalid named arguments in patterns

This test assesses hints in error messages for invalid argument names in patterns.
-/

inductive T where
  | mk1 (num : Nat) (str : String)
  | mk2 (x y z : Bool)

/--
error: Invalid argument name `w` for function `T.mk2`

Hint: Perhaps you meant one of the following parameter names:
  • `x`: w̵x̲
-/
#guard_msgs in
example (t : T) :=
  match t with
  | .mk2 (y := true) (w := true) (z := false) => ()
  | _ => ()

/--
error: Invalid argument name `w` for function `T.mk2`

Hint: Replace `w` with one of the following parameter names:
  • `x`: w̵x̲
-/
#guard_msgs in
example (t : T) :=
  match t with
  | T.mk2 (y := true) (w := true) (z := false) => ()
  | _ => ()

/-- error: Invalid pattern: Too many arguments to `T.mk2`; expected 3 explicit arguments -/
#guard_msgs in
example (t : T) :=
  match t with
  | T.mk2 a b (y := true) (z := false) (w := true) => ()
  | _ => ()

/--
error: Invalid argument names `n` and `s` for function `T.mk1`

Hint: Replace `n` with one of the following parameter names:
  • `num`: nu̲m̲
  • `str`: n̵s̲t̲r̲
-/
#guard_msgs in
example (t : T) :=
  match t with
  | T.mk1 (n := 17) (s := "hi") => ()
  | _ => ()

-- Ensure we don't offer hints for synthetic syntax:
macro "make_synthetic_bad_match" : command => `(
  example (t : T) :=
    match t with
    | T.mk1 (m := 0) (n := 1) .. => ()
    | _ => ()
)
/--
error: Invalid argument names `m` and `n` for function `T.mk1✝`

Hint: Perhaps you meant one of the following parameter names: `num` or `str`
-/
#guard_msgs in
make_synthetic_bad_match
