import Lean
open Lean

/-- Build an `Expr` for the list `[1, 2, ..., n]` of type `List Nat`. -/
partial def mkRangeListExpr (n : Nat) : Expr :=
  let natExpr := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [.zero]) natExpr
  let cons := fun (head tail : Expr) => mkApp3 (mkConst ``List.cons [.zero]) natExpr head tail
  let rec mkList (i : Nat) (acc : Expr) : Expr :=
    if i == 0 then acc
    else mkList (i - 1) (cons (mkNatLit i) acc)
  mkList n nil

/-- Build an `Expr` for the list `[n, n-1, ..., 1]` of type `List Nat`. -/
partial def mkRevRangeListExpr (n : Nat) : Expr :=
  let natExpr := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [.zero]) natExpr
  let cons := fun (head tail : Expr) => mkApp3 (mkConst ``List.cons [.zero]) natExpr head tail
  let rec mkList (i : Nat) (acc : Expr) : Expr :=
    if i == 0 then acc
    else mkList (i - 1) (cons (mkNatLit (n - i + 1)) acc)
  mkList n nil

/-- Build the expression `List.mergeSort [n, ..., 1] Nat.ble`. -/
def mkMergeSortProblem (n : Nat) : Expr :=
  let natExpr := mkConst ``Nat
  let list := mkRevRangeListExpr n
  let le := mkConst ``Nat.ble
  mkApp3 (mkConst ``List.mergeSort [.zero]) natExpr list le

def runProblem (n : Nat) : MetaM Unit := do
  let problem := mkMergeSortProblem n
  let startTime ← IO.monoNanosNow
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry problem
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  match executed with
  | .rfl _ => IO.println s!"mergeSort_{n}: {ms} ms (rfl)"
  | .step _ proof _ =>
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel proof
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"mergeSort_{n}: cbv {ms} ms, kernel {kernelMs} ms"

def runBenchmarks : MetaM Unit := do
  IO.println "=== Merge Sort CBV Benchmarks ==="
  IO.println ""
  for n in [10, 25, 50, 75, 100, 125, 175] do
    runProblem n
