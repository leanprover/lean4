/-!
Tests that the `match` compiler treats `Float` and `Float32` literals as match values, just like
`String`, `UInt64`, etc.

Matching uses the `DecidableEq` instance (propositional, bit-pattern equality), *not* IEEE `BEq`.
These differ: `BEq` says `0.0 == -0.0` and `NaN != NaN`, whereas the match compiler distinguishes
`0.0` from `-0.0` (different bit patterns) and would treat `NaN` as equal to itself.
-/

-- The match compiler relies on this instance (bit equality), which disagrees with IEEE `BEq`.
example : ((0.0 : Float) == (-0.0 : Float)) = true := rfl   -- IEEE `BEq`: equal
#guard (0.0 : Float) ≠ (-0.0 : Float)                       -- `DecidableEq`: not equal

def isFiveOh : Float → Bool
  | 5 => true
  | 6.0 => true
  | _ => false

/-- info: true -/
#guard_msgs in #eval isFiveOh 5.0
/-- info: true -/
#guard_msgs in #eval isFiveOh 6.0
/-- info: false -/
#guard_msgs in #eval isFiveOh 7.0

-- `0.0` and `-0.0` are distinct patterns (distinct bit patterns), demonstrating that the match
-- compiles to `DecidableEq` and not IEEE `BEq` (which would consider them equal).
def signOfZero : Float → String
  | 0.0 => "positive zero"
  | -0.0 => "negative zero"
  | _ => "nonzero"

/-- info: "positive zero" -/
#guard_msgs in #eval signOfZero 0.0
/-- info: "negative zero" -/
#guard_msgs in #eval signOfZero (-0.0)
/-- info: "nonzero" -/
#guard_msgs in #eval signOfZero 1.0

-- Negative (`Neg.neg`) literal patterns.
def classify : Float → String
  | -1.5 => "minus one and a half"
  | 2 => "two"
  | -3 => "minus three"
  | _ => "other"

/-- info: "minus one and a half" -/
#guard_msgs in #eval classify (-1.5)
/-- info: "two" -/
#guard_msgs in #eval classify 2.0
/-- info: "minus three" -/
#guard_msgs in #eval classify (-3.0)
/-- info: "other" -/
#guard_msgs in #eval classify 4.0

def classify32 : Float32 → String
  | 1.5 => "onehalf"
  | -2 => "minustwo"
  | _ => "other"

/-- info: "onehalf" -/
#guard_msgs in #eval classify32 1.5
/-- info: "minustwo" -/
#guard_msgs in #eval classify32 (-2.0)
/-- info: "other" -/
#guard_msgs in #eval classify32 3.0

-- `match h : f with` gives `h` the clean type `f = <literal>`; no model/bit-pattern internals leak.
-- (The type-ascription mismatch reveals the actual type of `h`.)
/--
error: Type mismatch
  h
has type
  f = 6.0
but is expected to have type
  True
-/
#guard_msgs in
example (f : Float) : Bool :=
  match h : f with
  | 6.0 => (h : True)
  | _ => false

-- no warning for overlaps due to lack of normalization for Float literals:

#guard_msgs in
example : Float → Bool
  | 5 => true
  | 5.0 => false
  | _ => false
