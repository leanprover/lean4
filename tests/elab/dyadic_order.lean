import Lean

/-!
Tests the `Ord` instance on `Dyadic` and the lawfulness classes derived from it. `compare` is
`compareOfLessAndEq`, so the main check is that it agrees with the existing `<` and `≤` and that
the kernel and the compiled code agree on it.
-/

open Lean Meta Elab Command

/-! The `Ord` instance and its lawfulness classes are available. -/

example : Ord Dyadic := inferInstance
example : Std.IsLinearOrder Dyadic := inferInstance
example : Std.LawfulOrderLT Dyadic := inferInstance
example : Std.LawfulOrderOrd Dyadic := inferInstance
example : Std.TransOrd Dyadic := inferInstance
example : Std.LawfulEqOrd Dyadic := inferInstance

/-! `compare` is definitionally `compareOfLessAndEq`, and the laws relate it to `<`, `≤` and `=`. -/

example (a b : Dyadic) : compare a b = compareOfLessAndEq a b := rfl
example (a b : Dyadic) : compare a b = .lt ↔ a < b := Std.compare_eq_lt
example (a b : Dyadic) : compare a b = .eq ↔ a = b := Std.compare_eq_eq_iff_eq
example (a b : Dyadic) : compare a b = .gt ↔ b < a := Std.compare_eq_gt
example (a b : Dyadic) : (compare a b).isLE ↔ a ≤ b := Std.LawfulOrderOrd.isLE_compare a b
example (a b c : Dyadic) (h₁ : compare a b = .lt) (h₂ : compare b c = .lt) : compare a c = .lt :=
  Std.TransCmp.lt_trans h₁ h₂

/-! The comparison evaluates by `decide` and at runtime. -/

example : compare (1 : Dyadic) 2 = .lt := by decide
example : compare (2 : Dyadic) 2 = .eq := by decide
example : compare (3 : Dyadic) 2 = .gt := by decide
example : compare (Dyadic.ofIntWithPrec 1 1) (Dyadic.ofIntWithPrec 3 2) = .lt := by decide
example : compare (Dyadic.ofIntWithPrec 2 1) (Dyadic.ofIntWithPrec 4 2) = .eq := by decide

/-- info: [Ordering.lt, Ordering.eq, Ordering.gt] -/
#guard_msgs in
#eval [compare (1 : Dyadic) 2, compare (2 : Dyadic) 2, compare (3 : Dyadic) 2]

/-!
Systematic comparison of the kernel and the runtime. `compare` has no runtime-specific
implementation, but `Dyadic.blt` and `decEq` go through `Int` arithmetic that the compiler and the
kernel implement separately, so the table is computed by the compiled code and then re-checked by
the kernel.
-/

/-- Integers and precisions on a small grid, so that many pairs are equal, including pairs built
from different `(integer, precision)` inputs that normalize to the same dyadic. -/
def values : List Dyadic :=
  [-6, -3, -1, 0, 1, 2, 3, 6].flatMap fun n =>
    [-2, -1, 0, 1, 2, 3].map fun prec => Dyadic.ofIntWithPrec n prec

def pairs : List (Dyadic × Dyadic) :=
  values.flatMap fun a => values.map (a, ·)

abbrev Summary := Bool × Bool × Ordering × Bool

def summary (a b : Dyadic) : Summary :=
  (decide (a < b), decide (a ≤ b), compare a b, decide (a = b))

def table : List Summary :=
  pairs.map fun (a, b) => summary a b

instance : ToExpr Ordering where
  toTypeExpr := mkConst ``Ordering
  toExpr
    | .lt => mkConst ``Ordering.lt
    | .eq => mkConst ``Ordering.eq
    | .gt => mkConst ``Ordering.gt

/-- info: 2304 pairs: 1098 lt, 108 eq, 1098 gt -/
#guard_msgs in
run_cmd liftTermElabM do
  let atRuntime := table
  let count (o : Ordering) := atRuntime.countP (·.2.2.1 == o)
  logInfo m!"{atRuntime.length} pairs: {count .lt} lt, {count .eq} eq, {count .gt} gt"
  -- Each summary must be consistent with the order laws at runtime as well.
  for (lt, le, c, eq) in atRuntime do
    unless (c == .lt) == lt && (c != .gt) == le && (c == .eq) == eq do
      throwError "inconsistent summary: {repr (lt, le, c, eq)}"
  let type ← mkEq (mkConst ``table) (toExpr atRuntime)
  addDecl <| .thmDecl {
    name := `table_eq_runtime
    levelParams := []
    type
    value := ← mkDecideProof type }
