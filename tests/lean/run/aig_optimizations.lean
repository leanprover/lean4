import Std.Tactic.BVDecide.Bitblast.BVExpr

open Std.Sat
open Std.Tactic.BVDecide

def mkFalseCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkFalseCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval (mkFalseCollapsible 1).bitblast.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval (mkFalseCollapsible 16).bitblast.aig.decls

def mkTrueCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const true
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval (mkTrueCollapsible 1).bitblast.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval (mkTrueCollapsible 16).bitblast.aig.decls

def mkConstantCollapsible (n : Nat) : BVLogicalExpr :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and (.gate .and tree tree) (.const false)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := (mkConstantCollapsible 1).bitblast
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := (mkConstantCollapsible 16).bitblast
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)
