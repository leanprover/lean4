import Lean.Data.Json
open Lean

/-!
Regression test for #15994: `JsonNumber.toString` wrote a zero mantissa with more than ten
decimals as `0.e-k`, which is not JSON, so `Json.compress` output for such a number did not read
back.
-/

/-- Parses `text` as a number, writes it with `Json.compress`, reads that back, and compares the
values. -/
def roundTrips (text : String) : Bool :=
  match Json.parse text with
  | .ok (.num n) =>
    match Json.parse (Json.num n).compress with
    | .ok (.num m) => compare n m == .eq
    | _ => false
  | _ => false

#guard roundTrips "0.0000000000"
#guard roundTrips "0.00000000000"
#guard roundTrips "0.000000000000000"
#guard roundTrips "-0.000000000000000"
#guard roundTrips "0.5"
#guard roundTrips "-0.000000000000125"
#guard roundTrips "1.25e-30"

#guard toString (⟨0, 15⟩ : JsonNumber) == "0"
#guard (Json.parse "[0.00000000000,1]").toOption.map Json.compress == some "[0,1]"
