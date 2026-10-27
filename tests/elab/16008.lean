import Lean.Data.Json

/-!
Regression test for #16008: `Json.parse` added the digits of a number to a big number one at a
time, which took time quadratic in the number of digits.
-/

open Lean

/-- `n` digits, cycling through all ten, starting with a nonzero one. -/
def digitsOf (n : Nat) : String :=
  String.ofList ((List.range n).map fun i => Char.ofNat (48 + (i * 7 + 3) % 10))

def valueMod (s : String) (p : Nat) : Nat :=
  s.foldl (fun n c => (10 * n + (c.toNat - 48)) % p) 0

/-!
Lengths around where the parser stops adding one digit at a time, and around the chunks of 18
digits it reads after that.
-/

#guard [1, 17, 18, 19, 35, 36, 37, 38, 54, 55, 56, 72, 73, 1000].all fun len =>
  let ds := digitsOf len
  match Json.parse ds, Json.parse ("-0." ++ ds), Json.parse ("0.000" ++ ds ++ "e2") with
  | .ok (.num ⟨m, 0⟩), .ok (.num ⟨m', e'⟩), .ok (.num ⟨m'', e''⟩) =>
    m == valueMod ds (10 ^ len) && m' == -m && e' == len && m'' == m && e'' == len + 1
  | _, _, _ => false

/-! A long run of digits, as an integer and as decimals. -/

#guard
  let ds := digitsOf 100000
  let p := 1000000007
  match Json.parse ds, Json.parse ("0." ++ ds) with
  | .ok (.num ⟨m, 0⟩), .ok (.num ⟨m', 100000⟩) =>
    m.toNat % p == valueMod ds p && m' == m
  | _, _ => false

/-!
Exponents are read the same way. A long positive one is read in full before the limit on its size
rejects it; a negative one has no limit.
-/

/-- info: Except.error "offset 100002: exponent too large" -/
#guard_msgs in
#eval Json.parse ("1e" ++ digitsOf 100000) |>.map (·.compress)

#guard
  let ds := digitsOf 100000
  match Json.parse ("1e-" ++ ds) with
  | .ok (.num ⟨1, e⟩) => e % 1000000007 == valueMod ds 1000000007
  | _ => false
