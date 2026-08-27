import Lean

/-!
The kernel must reject a mutual block that declares the same name twice.

`add_mutual` checked each member's name with `check_name`, which only looks at the pre-existing
environment — the block's own names are not there yet. So a duplicate passed, every member was
added in turn, and the last insert overwrote the others. The checks performed on the overwritten
members were then meaningless.

`add_mutual` rejects `safe` declarations outright, so the members here are `partial`.
-/

open Lean

private def mkDefn (n : Name) (type value : Expr) : DefinitionVal :=
  { name := n, levelParams := [], type, value, hints := .opaque, safety := .partial }

/-- info: mutual block with distinct names: ok -/
#guard_msgs in
#eval show CoreM Unit from do
  addDecl <| .mutualDefnDecl [
    mkDefn `mdistinctA (mkConst ``Nat) (mkRawNatLit 0),
    mkDefn `mdistinctB (mkConst ``Bool) (mkConst ``Bool.true)]
  IO.println "mutual block with distinct names: ok"

/--
error: (kernel) invalid mutual definition, duplicate declaration name 'mdup'
-/
#guard_msgs in
#eval show CoreM Unit from
  addDecl <| .mutualDefnDecl [
    mkDefn `mdup (mkConst ``Nat) (mkRawNatLit 0),
    mkDefn `mdup (mkConst ``Bool) (mkConst ``Bool.true)]

/-! A name already in the environment is still rejected by the pre-existing `check_name`. -/

/-- error: (kernel) constant has already been declared 'mdistinctA' -/
#guard_msgs in
#eval show CoreM Unit from
  addDecl <| .mutualDefnDecl [mkDefn `mdistinctA (mkConst ``Nat) (mkRawNatLit 0)]
