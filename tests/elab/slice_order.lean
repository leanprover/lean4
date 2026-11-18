import Lean

/-!
Tests the `LT`, `LE`, `BEq` and `Ord` instances on `String.Slice` and the
`Std.LinearPreorderPackage` built from them. Slices are compared by their contents, so the order is
only a preorder: slices of different strings with the same contents compare as equal.
-/

open Lean Meta Elab Command
open String (Slice)

/-! The order instances and their lawfulness classes are available. -/

example : Std.LinearPreorderPackage Slice := inferInstance
example : Std.IsLinearPreorder Slice := inferInstance
example : Std.LawfulOrderLT Slice := inferInstance
example : Std.LawfulOrderOrd Slice := inferInstance
example : Std.LawfulOrderBEq Slice := inferInstance
example : Std.TransOrd Slice := inferInstance
example : Min Slice := inferInstance
example : Max Slice := inferInstance
example : Std.LawfulOrderLeftLeaningMin Slice := inferInstance
example : Std.LawfulOrderLeftLeaningMax Slice := inferInstance
example : Std.LawfulOrderMin Slice := inferInstance
example : Std.LawfulOrderMax Slice := inferInstance

example (s t : Slice) : s < t ↔ s.copy < t.copy := by simp
example (s t : Slice) : s ≤ t ↔ s.copy ≤ t.copy := by simp
example (s t : Slice) : compare s t = compare s.copy t.copy := by simp
example (s t : Slice) : s ≤ t ∨ t ≤ s := Std.le_total
example (s t : Slice) : ¬ s < t ↔ t ≤ s := Std.not_lt
example (s t : Slice) : compare s t = .lt ↔ s < t := Std.compare_eq_lt
example (s t : Slice) : compare s t = .eq ↔ s == t := Std.compare_eq_eq
example (s t u : Slice) (h₁ : s ≤ t) (h₂ : t ≤ u) : s ≤ u := Std.le_trans h₁ h₂

/-! `≤` is the non-strict version of `<`. It used to be the negation of `<`. -/

#guard "abc".toSlice ≤ "abd".toSlice
#guard !("abd".toSlice ≤ "abc".toSlice)
#guard "abc".toSlice ≤ "abc".toSlice
#guard "ab".toSlice ≤ "abc".toSlice
#guard !("abc".toSlice ≤ "ab".toSlice)
#guard "".toSlice ≤ "".toSlice
#guard "abd".toSlice ≥ "abc".toSlice
#guard !("abc".toSlice ≥ "abd".toSlice)

/-! Slices are compared by content, regardless of their underlying strings and offsets. -/

#guard compare "ab".toSlice ("xab".toSlice.drop 1) == .eq
#guard "ab".toSlice ≤ "xab".toSlice.drop 1 && "xab".toSlice.drop 1 ≤ "ab".toSlice
#guard !("ab".toSlice < "xab".toSlice.drop 1)
#guard compare ("€a".toSlice.drop 1) "b".toSlice == .lt
#guard compare ("xé".toSlice.drop 1) ("ÿ".toSlice) == .lt
#guard compare ("x\x7f".toSlice.drop 1) ("é".toSlice) == .lt
#guard ("é".toSlice) > ("x\x7f".toSlice.drop 1)
#guard compare ("abcd".toSlice.take 2) ("abc".toSlice) == .lt
#guard compare ("abc".toSlice) ("abcd".toSlice.take 2) == .gt
#guard ("abcd".toSlice.take 2) < ("abc".toSlice)
#guard !(("abc".toSlice) < ("abcd".toSlice.take 2))

/-! The decision procedures are implemented using `memcmp`. -/

/--
info: String.Slice.Pattern.Internal.memcmpStr: (some lean_string_memcmp)
String.Slice.Pattern.Internal.memcmpStrLt: (some lean_string_memcmp_lt)
String.Slice.Pattern.Internal.memcmpStrCompare: (some lean_string_memcmp_compare)
-/
#guard_msgs in
#eval show CoreM Unit from do
  for n in [``String.Slice.Pattern.Internal.memcmpStr, ``String.Slice.Pattern.Internal.memcmpStrLt,
      ``String.Slice.Pattern.Internal.memcmpStrCompare] do
    IO.println s!"{n}: {getExternNameFor (← getEnv) `c n}"

/-!
`<`, `≤` and `compare` compile to direct calls rather than being dispatched through the
`LinearPreorderPackage` instance.
-/

/--
trace: [Compiler.IR] [result]
    def lt (x_1 : @& obj) (x_2 : @& obj) : u8 :=
      let x_3 : u8 := String.Slice.blt x_1 x_2;
      ret x_3
    def lt._boxed (x_1 : obj) (x_2 : obj) : tagged :=
      let x_3 : u8 := lt x_1 x_2;
      dec x_2;
      dec x_1;
      let x_4 : tagged := box x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def lt (s t : Slice) : Bool := s < t

/--
trace: [Compiler.IR] [result]
    def le (x_1 : @& obj) (x_2 : @& obj) : u8 :=
      let x_3 : u8 := String.Slice.instDecidableLE x_1 x_2;
      ret x_3
    def le._boxed (x_1 : obj) (x_2 : obj) : tagged :=
      let x_3 : u8 := le x_1 x_2;
      dec x_2;
      dec x_1;
      let x_4 : tagged := box x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def le (s t : Slice) : Bool := s ≤ t

/--
trace: [Compiler.IR] [result]
    def cmp (x_1 : @& obj) (x_2 : @& obj) : u8 :=
      let x_3 : u8 := String.Slice.compare x_1 x_2;
      ret x_3
    def cmp._boxed (x_1 : obj) (x_2 : obj) : tagged :=
      let x_3 : u8 := cmp x_1 x_2;
      dec x_2;
      dec x_1;
      let x_4 : tagged := box x_3;
      ret x_4
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def cmp (s t : Slice) : Ordering := compare s t
