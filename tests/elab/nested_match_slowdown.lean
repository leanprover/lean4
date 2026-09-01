/-
Regression test for slow elaboration of incomplete matches on types with
many constructors and multi-constructor fields. Without the
`match.maxCounterExamples` limit, the match compiler would case-split every
field variable, producing O(K^fields) counter-examples per missing
constructor (where K is the number of constructors of the field type).

For `Op w` (20 constructors, each with two `Operand w` fields having 8
constructors), a `nomatch` would try to generate 20 × 8² = 1280
counter-examples. The limit caps this at 5 (by default).
-/
set_option autoImplicit false

-- A field type with many constructors
inductive Operand (w : Nat) where
  | r0 : Nat → Operand w
  | r1 : Nat → Operand w
  | r2 : Nat → Operand w
  | r3 : Nat → Operand w
  | r4 : Nat → Operand w
  | r5 : Nat → Operand w
  | r6 : Nat → Operand w
  | r7 : Nat → Operand w

-- A large inductive with multi-constructor field types (20 constructors)
inductive Op (w : Nat) where
  | add : Operand w → Operand w → Op w
  | or_ : Operand w → Operand w → Op w
  | xor : Operand w → Operand w → Op w
  | sub : Operand w → Operand w → Op w
  | mul : Operand w → Operand w → Op w
  | shl : Operand w → Operand w → Op w
  | shr : Operand w → Operand w → Op w
  | mov : Operand w → Operand w → Op w
  | cmp : Operand w → Operand w → Op w
  | test : Operand w → Operand w → Op w
  | lea : Operand w → Operand w → Op w
  | c11 : Operand w → Operand w → Op w
  | c12 : Operand w → Operand w → Op w
  | c13 : Operand w → Operand w → Op w
  | c14 : Operand w → Operand w → Op w
  | c15 : Operand w → Operand w → Op w
  | c16 : Operand w → Operand w → Op w
  | c17 : Operand w → Operand w → Op w
  | c18 : Operand w → Operand w → Op w
  | c19 : Operand w → Operand w → Op w

-- Without the counter-example limit, this `nomatch` would generate 1280
-- counter-examples and take several seconds. With the limit (default 5),
-- it stops early and reports the first 5 missing cases quickly.
/--
error: Missing cases:
(add (Operand.r0 _) (Operand.r0 _))
(add (Operand.r0 _) (Operand.r1 _))
(add (Operand.r0 _) (Operand.r2 _))
(add (Operand.r0 _) (Operand.r3 _))
(add (Operand.r0 _) (Operand.r4 _))
(further cases omitted, increase `set_option match.maxCounterExamples 5` to see more)
-/
#guard_msgs in
def Op.testNomatch {w : Nat} (op : Op w) : Nat := nomatch op

-- Regression test: recursive single-constructor types terminate in counter-example
-- generation. The recursive type check in `processConstructor` prevents infinite
-- unfolding. This `nomatch` should fail quickly with "missing cases".
inductive RecStruct where
  | mk : Nat → RecStruct → RecStruct

/--
error: Missing cases:
_
-/
#guard_msgs in
def recTest (x : RecStruct) : Nat := nomatch x
