import Std.Tactic.BVDecide.Bitblast.BoolExpr

open Std.Sat
open Std.Tactic.BVDecide

def mkSharedTree (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .literal 0
  | n + 1 =>
    let tree := mkSharedTree n
    .gate .xor tree tree

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.gate 0 1 true true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 1) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.gate 0 1 true true,
  Std.Sat.AIG.Decl.gate 2 2 true true, Std.Sat.AIG.Decl.gate 2 3 true true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 2) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.gate 0 1 true true,
  Std.Sat.AIG.Decl.gate 2 2 true true, Std.Sat.AIG.Decl.gate 2 3 true true, Std.Sat.AIG.Decl.gate 4 4 true true,
  Std.Sat.AIG.Decl.gate 4 5 true true, Std.Sat.AIG.Decl.gate 6 6 true true, Std.Sat.AIG.Decl.gate 6 7 true true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 4) AIG.mkAtomCached |>.aig.decls

/--
info: #[Std.Sat.AIG.Decl.atom 0, Std.Sat.AIG.Decl.gate 0 0 true true, Std.Sat.AIG.Decl.gate 0 1 true true,
  Std.Sat.AIG.Decl.gate 2 2 true true, Std.Sat.AIG.Decl.gate 2 3 true true, Std.Sat.AIG.Decl.gate 4 4 true true,
  Std.Sat.AIG.Decl.gate 4 5 true true, Std.Sat.AIG.Decl.gate 6 6 true true, Std.Sat.AIG.Decl.gate 6 7 true true,
  Std.Sat.AIG.Decl.gate 8 8 true true, Std.Sat.AIG.Decl.gate 8 9 true true, Std.Sat.AIG.Decl.gate 10 10 true true,
  Std.Sat.AIG.Decl.gate 10 11 true true, Std.Sat.AIG.Decl.gate 12 12 true true, Std.Sat.AIG.Decl.gate 12 13 true true,
  Std.Sat.AIG.Decl.gate 14 14 true true, Std.Sat.AIG.Decl.gate 14 15 true true, Std.Sat.AIG.Decl.gate 16 16 true true,
  Std.Sat.AIG.Decl.gate 16 17 true true, Std.Sat.AIG.Decl.gate 18 18 true true, Std.Sat.AIG.Decl.gate 18 19 true true,
  Std.Sat.AIG.Decl.gate 20 20 true true, Std.Sat.AIG.Decl.gate 20 21 true true, Std.Sat.AIG.Decl.gate 22 22 true true,
  Std.Sat.AIG.Decl.gate 22 23 true true, Std.Sat.AIG.Decl.gate 24 24 true true, Std.Sat.AIG.Decl.gate 24 25 true true,
  Std.Sat.AIG.Decl.gate 26 26 true true, Std.Sat.AIG.Decl.gate 26 27 true true, Std.Sat.AIG.Decl.gate 28 28 true true,
  Std.Sat.AIG.Decl.gate 28 29 true true, Std.Sat.AIG.Decl.gate 30 30 true true, Std.Sat.AIG.Decl.gate 30 31 true true]
-/
#guard_msgs in
#eval ofBoolExprCached (mkSharedTree 16) AIG.mkAtomCached |>.aig.decls
