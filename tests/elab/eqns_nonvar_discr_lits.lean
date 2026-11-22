/-!
Equation lemmas of a definition by `match` where a discriminant is a pair of literals and another
one is a variable, for each type of literal.

In `stmt*`, the first alternative is unreachable: its case has the hypothesis
`(1, a) = (fst, b)`, where `a` and `b` are different literals, and no equation is generated for it.
In `proof*`, the proof of the equation for the last alternative splits the `match` again, and the
case of the third alternative has the hypothesis `(a, b) = (z, snd)`, which is refuted.
-/

def stmtNat (s : String) : Nat :=
  match (1, (10 : Nat)), s with
  | (_, (20 : Nat)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtNat.eq_1 : ∀ (s_1 : String), stmtNat s_1 = 2
-/
#guard_msgs in
#print equations stmtNat

def proofNat (s : String) : Nat :=
  match ((10 : Nat), (20 : Nat)), s with
  | (10, 30), _ => 1
  | (10, 20), "x" => 2
  | (30, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofNat.eq_1 : proofNat "x" = 2
theorem proofNat.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofNat s_1 = 4
-/
#guard_msgs in
#print equations proofNat

def stmtInt (s : String) : Nat :=
  match (1, (10 : Int)), s with
  | (_, (20 : Int)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtInt.eq_1 : ∀ (s_1 : String), stmtInt s_1 = 2
-/
#guard_msgs in
#print equations stmtInt

def proofInt (s : String) : Nat :=
  match ((10 : Int), (20 : Int)), s with
  | (10, -3), _ => 1
  | (10, 20), "x" => 2
  | (-3, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofInt.eq_1 : proofInt "x" = 2
theorem proofInt.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofInt s_1 = 4
-/
#guard_msgs in
#print equations proofInt

def stmtFin (s : String) : Nat :=
  match (1, (1 : Fin 5)), s with
  | (_, (2 : Fin 5)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtFin.eq_1 : ∀ (s_1 : String), stmtFin s_1 = 2
-/
#guard_msgs in
#print equations stmtFin

def proofFin (s : String) : Nat :=
  match ((1 : Fin 5), (2 : Fin 5)), s with
  | (1, 3), _ => 1
  | (1, 2), "x" => 2
  | (3, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofFin.eq_1 : proofFin "x" = 2
theorem proofFin.eq_2 : ∀ (s_1 : String), ((1, 2) = (1, 2) → s_1 = "x" → False) → proofFin s_1 = 4
-/
#guard_msgs in
#print equations proofFin

def stmtBitVec (s : String) : Nat :=
  match (1, (1#8 : BitVec 8)), s with
  | (_, (2#8 : BitVec 8)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtBitVec.eq_1 : ∀ (s_1 : String), stmtBitVec s_1 = 2
-/
#guard_msgs in
#print equations stmtBitVec

def proofBitVec (s : String) : Nat :=
  match ((1#8 : BitVec 8), (2#8 : BitVec 8)), s with
  | (1#8, 3#8), _ => 1
  | (1#8, 2#8), "x" => 2
  | (3#8, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofBitVec.eq_1 : proofBitVec "x" = 2
theorem proofBitVec.eq_2 : ∀ (s_1 : String), ((1#8, 2#8) = (1#8, 2#8) → s_1 = "x" → False) → proofBitVec s_1 = 4
-/
#guard_msgs in
#print equations proofBitVec

def stmtString (s : String) : Nat :=
  match (1, ("a" : String)), s with
  | (_, ("b" : String)), "x" => 1
  | _, _ => 2

/--
info: equations:
theorem stmtString.eq_1 : ∀ (s_1 : String),
  (∀ (fst : Nat), (1, "a") = (fst, "b") → s_1 = "x" → False) → stmtString s_1 = 2
-/
#guard_msgs in
#print equations stmtString

def proofString (s : String) : Nat :=
  match (("a" : String), ("b" : String)), s with
  | ("a", "z"), _ => 1
  | ("a", "b"), "x" => 2
  | ("z", _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofString.eq_1 : proofString "x" = 2
theorem proofString.eq_2 : ∀ (s_1 : String), (("a", "b") = ("a", "b") → s_1 = "x" → False) → proofString s_1 = 4
-/
#guard_msgs in
#print equations proofString

def stmtChar (s : String) : Nat :=
  match (1, ('a' : Char)), s with
  | (_, ('b' : Char)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtChar.eq_1 : ∀ (s_1 : String), stmtChar s_1 = 2
-/
#guard_msgs in
#print equations stmtChar

def proofChar (s : String) : Nat :=
  match (('a' : Char), ('b' : Char)), s with
  | ('a', 'z'), _ => 1
  | ('a', 'b'), "x" => 2
  | ('z', _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofChar.eq_1 : proofChar "x" = 2
theorem proofChar.eq_2 : ∀ (s_1 : String), (('a', 'b') = ('a', 'b') → s_1 = "x" → False) → proofChar s_1 = 4
-/
#guard_msgs in
#print equations proofChar

def stmtUInt8 (s : String) : Nat :=
  match (1, (10 : UInt8)), s with
  | (_, (20 : UInt8)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtUInt8.eq_1 : ∀ (s_1 : String), stmtUInt8 s_1 = 2
-/
#guard_msgs in
#print equations stmtUInt8

def proofUInt8 (s : String) : Nat :=
  match ((10 : UInt8), (20 : UInt8)), s with
  | (10, 30), _ => 1
  | (10, 20), "x" => 2
  | (30, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofUInt8.eq_1 : proofUInt8 "x" = 2
theorem proofUInt8.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofUInt8 s_1 = 4
-/
#guard_msgs in
#print equations proofUInt8

def stmtUInt16 (s : String) : Nat :=
  match (1, (10 : UInt16)), s with
  | (_, (20 : UInt16)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtUInt16.eq_1 : ∀ (s_1 : String), stmtUInt16 s_1 = 2
-/
#guard_msgs in
#print equations stmtUInt16

def proofUInt16 (s : String) : Nat :=
  match ((10 : UInt16), (20 : UInt16)), s with
  | (10, 30), _ => 1
  | (10, 20), "x" => 2
  | (30, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofUInt16.eq_1 : proofUInt16 "x" = 2
theorem proofUInt16.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofUInt16 s_1 = 4
-/
#guard_msgs in
#print equations proofUInt16

def stmtUInt32 (s : String) : Nat :=
  match (1, (10 : UInt32)), s with
  | (_, (20 : UInt32)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtUInt32.eq_1 : ∀ (s_1 : String), stmtUInt32 s_1 = 2
-/
#guard_msgs in
#print equations stmtUInt32

def stmtUInt64 (s : String) : Nat :=
  match (1, (10 : UInt64)), s with
  | (_, (20 : UInt64)), "x" => 1
  | _, _ => 2

/--
info: equations:
@[backward_defeq] theorem stmtUInt64.eq_1 : ∀ (s_1 : String), stmtUInt64 s_1 = 2
-/
#guard_msgs in
#print equations stmtUInt64

def proofUInt32 (s : String) : Nat :=
  match ((10 : UInt32), (20 : UInt32)), s with
  | (10, 30), _ => 1
  | (10, 20), "x" => 2
  | (30, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofUInt32.eq_1 : proofUInt32 "x" = 2
theorem proofUInt32.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofUInt32 s_1 = 4
-/
#guard_msgs in
#print equations proofUInt32

def proofUInt64 (s : String) : Nat :=
  match ((10 : UInt64), (20 : UInt64)), s with
  | (10, 30), _ => 1
  | (10, 20), "x" => 2
  | (30, _), _ => 3
  | _, _ => 4

/--
info: equations:
theorem proofUInt64.eq_1 : proofUInt64 "x" = 2
theorem proofUInt64.eq_2 : ∀ (s_1 : String), ((10, 20) = (10, 20) → s_1 = "x" → False) → proofUInt64 s_1 = 4
-/
#guard_msgs in
#print equations proofUInt64
