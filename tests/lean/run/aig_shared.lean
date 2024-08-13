import Lean.Elab.Tactic.BvDecide.BitBlast.BoolExpr

open Std.Sat
open Lean.Elab.Tactic.BvDecide

def mkSharedTree (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .literal 0
  | n + 1 =>
    let tree := mkSharedTree n
    .gate .or tree tree

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.const true,
  Std.Sat.AIG.Decl.gate 1 2 true false]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 1) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.const true,
  Std.Sat.AIG.Decl.gate 1 2 true false, Std.Sat.AIG.Decl.gate 3 3 true true, Std.Sat.AIG.Decl.gate 2 4 false true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 2) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.const true,
  Std.Sat.AIG.Decl.gate 1 2 true false, Std.Sat.AIG.Decl.gate 3 3 true true, Std.Sat.AIG.Decl.gate 2 4 false true,
  Std.Sat.AIG.Decl.gate 5 5 true true, Std.Sat.AIG.Decl.gate 2 6 false true, Std.Sat.AIG.Decl.gate 7 7 true true,
  Std.Sat.AIG.Decl.gate 2 8 false true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 4) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.const true,
  Std.Sat.AIG.Decl.gate 1 2 true false, Std.Sat.AIG.Decl.gate 3 3 true true, Std.Sat.AIG.Decl.gate 2 4 false true,
  Std.Sat.AIG.Decl.gate 5 5 true true, Std.Sat.AIG.Decl.gate 2 6 false true, Std.Sat.AIG.Decl.gate 7 7 true true,
  Std.Sat.AIG.Decl.gate 2 8 false true, Std.Sat.AIG.Decl.gate 9 9 true true, Std.Sat.AIG.Decl.gate 2 10 false true,
  Std.Sat.AIG.Decl.gate 11 11 true true, Std.Sat.AIG.Decl.gate 2 12 false true, Std.Sat.AIG.Decl.gate 13 13 true true,
  Std.Sat.AIG.Decl.gate 2 14 false true, Std.Sat.AIG.Decl.gate 15 15 true true, Std.Sat.AIG.Decl.gate 2 16 false true,
  Std.Sat.AIG.Decl.gate 17 17 true true, Std.Sat.AIG.Decl.gate 2 18 false true, Std.Sat.AIG.Decl.gate 19 19 true true,
  Std.Sat.AIG.Decl.gate 2 20 false true, Std.Sat.AIG.Decl.gate 21 21 true true, Std.Sat.AIG.Decl.gate 2 22 false true,
  Std.Sat.AIG.Decl.gate 23 23 true true, Std.Sat.AIG.Decl.gate 2 24 false true, Std.Sat.AIG.Decl.gate 25 25 true true,
  Std.Sat.AIG.Decl.gate 2 26 false true, Std.Sat.AIG.Decl.gate 27 27 true true, Std.Sat.AIG.Decl.gate 2 28 false true,
  Std.Sat.AIG.Decl.gate 29 29 true true, Std.Sat.AIG.Decl.gate 2 30 false true, Std.Sat.AIG.Decl.gate 31 31 true true,
  Std.Sat.AIG.Decl.gate 2 32 false true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 16) AIG.mkAtomCached |>.aig.decls
