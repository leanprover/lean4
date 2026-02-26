import Lean
open Lean

partial def test (n : Nat) : IO Unit := do
  let rec go (e : Expr) (n : Nat) : IO Unit := do
    match n with
    | 0 => return ()
    | n+1 =>
      let eNew := mkApp (mkConst ``Nat.succ) e
      IO.println s!"{eNew.approxDepth}"
      assert! eNew.approxDepth >= e.approxDepth
      go eNew n
  go (mkConst ``Nat.zero) n

#eval test 500
