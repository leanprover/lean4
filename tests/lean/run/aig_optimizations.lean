import Std.Tactic.BVDecide.Bitblast

open Std.Sat
open Std.Tactic.BVDecide

def mkFalseCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkFalseCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.false] -/
#guard_msgs in
#eval BVLogicalExpr.bitblast (mkFalseCollapsible 1) |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.false] -/
#guard_msgs in
#eval BVLogicalExpr.bitblast (mkFalseCollapsible 16) |>.aig.decls

def mkTrueCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const true
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.false] -/
#guard_msgs in
#eval BVLogicalExpr.bitblast (mkTrueCollapsible 1) |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.false] -/
#guard_msgs in
#eval BVLogicalExpr.bitblast (mkTrueCollapsible 16) |>.aig.decls

def mkConstantCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and (.gate .and tree tree) (.const false)

/-- info: (1, Std.Sat.AIG.Decl.false) -/
#guard_msgs in
#eval
  let entry := BVLogicalExpr.bitblast (mkConstantCollapsible 1)
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)

/-- info: (1, Std.Sat.AIG.Decl.false) -/
#guard_msgs in
#eval
  let entry := BVLogicalExpr.bitblast (mkConstantCollapsible 16)
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)
