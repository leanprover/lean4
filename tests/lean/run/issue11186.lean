-- set_option trace.Meta.Match.match true
-- set_option trace.Meta.Match.debug true

/--
error: Failed to compile pattern matching: Stuck at
  remaining variables: [x✝:(String)]
  alternatives:
    [bytes✝:(ByteArray),
     isValidUTF8✝:(bytes✝.IsValidUTF8)] |- [(String.ofByteArray bytes✝ isValidUTF8✝)] => h_1 bytes✝ isValidUTF8✝
    [] |- ["Eek"] => h_2 ()
    [x✝:(String)] |- [x✝] => h_3 x✝
  examples:_
-/
#guard_msgs in
def stringMatch : Option Nat :=
  match "Bad" with
  | String.ofByteArray _ _ => some 1
  | "Eek" => some 2
  | _ => none -- used to be: unknown free variable `_fvar.149`

/--
error: Failed to compile pattern matching: Stuck at
  remaining variables: [x✝:(Char)]
  alternatives:
    [valid✝:(UInt32.isValidChar 5)] |- [(Char.mk 5 valid✝)] => h_1 valid✝
    [] |- ['A'] => h_2 ()
    [x✝:(Char)] |- [x✝] => h_3 x✝
  examples:_
-/
#guard_msgs in
def charMatch :=
  match 'X' with
  | Char.mk 5 _ => some 1
  | 'A' => some 2
  | _ => none -- used to be: unknown free variable `_fvar.836`

/--
error: Failed to compile pattern matching: Stuck at
  remaining variables: [x✝:(UInt8)]
  alternatives:
    [] |- [(UInt8.ofBitVec (BitVec.ofFin 3))] => h_1 ()
    [] |- [5] => h_2 ()
    [x✝:(UInt8)] |- [x✝] => h_3 x✝
  examples:_
-/
#guard_msgs in
def uInt8Match :=
  match (5: UInt8) with
  | UInt8.ofBitVec (BitVec.ofFin 3) => some 1
  | 5 => some 2
  | _ => none -- used to be: unknown free variable `_fvar.1026`
