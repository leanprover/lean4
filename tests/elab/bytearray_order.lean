import Lean

/-!
Tests the `LT`, `LE`, `BEq`, `Ord`, `Min` and `Max` instances on `ByteArray`. The runtime
implementations of `<`, `compare` and `==` use `memcmp`, so the main check here is that the kernel,
which evaluates the logical definitions in terms of `Array UInt8`, agrees with the results computed
at runtime.
-/

open Lean Meta Elab Command

/-! The order instances and their lawfulness classes are available. -/

example : Std.LinearOrderPackage ByteArray := inferInstance
example : Std.IsLinearOrder ByteArray := inferInstance
example : Std.LawfulOrderLT ByteArray := inferInstance
example : Std.LawfulOrderOrd ByteArray := inferInstance
example : Std.LawfulOrderBEq ByteArray := inferInstance
example : Std.LawfulOrderMin ByteArray := inferInstance
example : Std.LawfulOrderMax ByteArray := inferInstance
example : LawfulBEq ByteArray := inferInstance
example : Std.TransOrd ByteArray := inferInstance
example : Std.LawfulEqOrd ByteArray := inferInstance

example (a b : ByteArray) : a < b ↔ a.data < b.data := Iff.rfl
example (a b : ByteArray) : a ≤ b ↔ a.data ≤ b.data := Iff.rfl
example (a b : ByteArray) : compare a b = compare a.data b.data := rfl
example (a b : ByteArray) : a ≤ b ∨ b ≤ a := Std.le_total
example (a b : ByteArray) : ¬ a < b ↔ b ≤ a := Std.not_lt
example (a b : ByteArray) : compare a b = .lt ↔ a < b := Std.compare_eq_lt
example (a b : ByteArray) : compare a b = .eq ↔ a = b := Std.compare_eq_eq_iff_eq
example (a b : ByteArray) : (a == b) = true ↔ a = b := beq_iff_eq
example (a b : ByteArray) : min a b = if a ≤ b then a else b := Std.min_eq_ite
example (a b : ByteArray) : max a b = if b ≤ a then a else b := Std.max_eq_ite

/-! The decision procedures are implemented in the runtime. -/

/--
info: ByteArray.decidableLT: (some lean_byte_array_dec_lt)
ByteArray.compare: (some lean_byte_array_compare)
ByteArray.beq: (some lean_sarray_dec_eq)
ByteArray.decEq: (some lean_sarray_dec_eq)
-/
#guard_msgs in
#eval show CoreM Unit from do
  for n in [``ByteArray.decidableLT, ``ByteArray.compare, ``ByteArray.beq, ``ByteArray.decEq] do
    IO.println s!"{n}: {getExternNameFor (← getEnv) `c n}"

/-!
`≤` and `min` compile to direct calls rather than being dispatched through the
`LinearOrderPackage` instance.
-/

/--
trace: [Compiler.IR] [result]
    def le (x_1 : @& obj) (x_2 : @& obj) : u8 :=
      let x_3 : u8 := ByteArray.instDecidableLE x_1 x_2;
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
def le (a b : ByteArray) : Bool := a ≤ b

/--
trace: [Compiler.IR] [result]
    def mn (x_1 : @& obj) (x_2 : @& obj) : obj :=
      let x_3 : u8 := ByteArray.instDecidableLE x_1 x_2;
      case x_3 : u8 of
      Bool.false →
        inc x_2;
        ret x_2
      Bool.true →
        inc x_1;
        ret x_1
    def mn._boxed (x_1 : obj) (x_2 : obj) : obj :=
      let x_3 : obj := mn x_1 x_2;
      dec x_2;
      dec x_1;
      ret x_3
-/
#guard_msgs in
set_option trace.compiler.ir.result true in
def mn (a b : ByteArray) : ByteArray := min a b

/-! Some examples, computed at runtime, including bytes that a signed comparison gets wrong. -/

#guard ByteArray.empty < ⟨#[0]⟩
#guard ⟨#[0x7f]⟩ < (⟨#[0x80]⟩ : ByteArray)
#guard ⟨#[0x80]⟩ < (⟨#[0xff]⟩ : ByteArray)
#guard ⟨#[1, 2]⟩ < (⟨#[1, 2, 0]⟩ : ByteArray)
#guard ⟨#[1, 2, 0xff]⟩ < (⟨#[1, 3]⟩ : ByteArray)
#guard ¬ (⟨#[1, 2]⟩ : ByteArray) < ⟨#[1, 2]⟩
#guard (⟨#[1, 2]⟩ : ByteArray) ≤ ⟨#[1, 2]⟩
#guard ¬ (⟨#[0x80]⟩ : ByteArray) ≤ ⟨#[0x7f, 0xff]⟩
#guard compare (⟨#[0xff]⟩ : ByteArray) ⟨#[0x00, 0x00]⟩ == .gt
#guard compare (⟨#[1, 2, 3]⟩ : ByteArray) ⟨#[1, 2, 3]⟩ == .eq
#guard compare "abc".toUTF8 "abd".toUTF8 == .lt
#guard min (⟨#[0x80]⟩ : ByteArray) ⟨#[0x7f, 0xff]⟩ == ⟨#[0x7f, 0xff]⟩
#guard max (⟨#[0x80]⟩ : ByteArray) ⟨#[0x7f, 0xff]⟩ == ⟨#[0x80]⟩

/-! Some of these, checked by the kernel using the logical definitions. -/

example : compare (⟨#[0x7f]⟩ : ByteArray) ⟨#[0x80]⟩ = .lt := by decide +kernel
example : compare (⟨#[1, 2]⟩ : ByteArray) ⟨#[1, 2, 0]⟩ = .lt := by decide +kernel
example : compare (⟨#[0xff]⟩ : ByteArray) ⟨#[0x00, 0x00]⟩ = .gt := by decide +kernel
example : compare (⟨#[1, 2, 3]⟩ : ByteArray) ⟨#[1, 2, 3]⟩ = .eq := by decide +kernel
example : ((⟨#[1, 2]⟩ : ByteArray) == ⟨#[1, 2, 0]⟩) = false := by decide +kernel

/-!
Systematic comparison of the kernel and the runtime. The kernel cannot reduce `Array.lex`, so it
decides `<` and `≤` via the underlying `List.lt` instead.
-/

def short : List ByteArray :=
  [⟨#[]⟩, ⟨#[0x00]⟩, ⟨#[0x01]⟩, ⟨#[0x7f]⟩, ⟨#[0x80]⟩, ⟨#[0xff]⟩,
   ⟨#[0x00, 0x00]⟩, ⟨#[0x00, 0xff]⟩, ⟨#[0x7f, 0xff]⟩, ⟨#[0x80, 0x00]⟩, ⟨#[0xff, 0x00]⟩,
   ⟨#[1, 2]⟩, ⟨#[1, 2, 0]⟩, ⟨#[1, 2, 3]⟩, ⟨#[1, 2, 0x80]⟩, ⟨#[1, 3]⟩]

-- Built from `List` functions because the kernel is slow to reduce well-founded recursion.
def long (n : Nat) : ByteArray :=
  ⟨((List.range n).map fun i => (i * 37 + 11).toUInt8).toArray⟩

/-- All pairs of short byte arrays, and long byte arrays paired with variants that differ late. -/
def pairs : List (ByteArray × ByteArray) :=
  let variants (a : ByteArray) : List ByteArray :=
    [a, ⟨a.data.pop⟩, a.push 0, a.set! (a.size - 1) 0, a.set! (a.size - 1) 0xff]
  let withVariants (a : ByteArray) := (variants a).flatMap fun b => [(a, b), (b, a)]
  short.flatMap (fun a => short.map (a, ·)) ++ withVariants (long 17)

abbrev Summary := Bool × Bool × Ordering × Bool × Bool

/-- Uses the regular instances, which call into the runtime when evaluated. -/
def viaInstances (a b : ByteArray) : Summary :=
  (decide (a < b), decide (a ≤ b), compare a b, a == b, decide (a = b))

/-- Uses instances that the kernel can evaluate. For `compare`, `==` and `=`, these are the regular
instances, whose runtime implementation the kernel ignores. -/
def viaKernel (a b : ByteArray) : Summary :=
  (@decide (a < b) (inferInstanceAs (Decidable (a.data.toList < b.data.toList))),
   @decide (a ≤ b) (inferInstanceAs (Decidable (¬ b.data.toList < a.data.toList))),
   compare a b, a == b, decide (a = b))

def table (f : ByteArray → ByteArray → Summary) : List Summary :=
  pairs.map fun (a, b) => f a b

instance : ToExpr Ordering where
  toTypeExpr := mkConst ``Ordering
  toExpr
    | .lt => mkConst ``Ordering.lt
    | .eq => mkConst ``Ordering.eq
    | .gt => mkConst ``Ordering.gt

/-- info: 266 pairs: 124 lt, 18 eq, 124 gt -/
#guard_msgs in
run_cmd liftTermElabM do
  let atRuntime := table viaInstances
  let count (o : Ordering) := atRuntime.countP (·.2.2.1 == o)
  logInfo m!"{atRuntime.length} pairs: {count .lt} lt, {count .eq} eq, {count .gt} gt"
  let type ← mkEq (mkApp (mkConst ``table) (mkConst ``viaKernel)) (toExpr atRuntime)
  addDecl <| .thmDecl {
    name := `table_viaKernel_eq_runtime
    levelParams := []
    type
    value := ← mkDecideProof type }
