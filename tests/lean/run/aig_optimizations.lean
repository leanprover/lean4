import Lean.Elab.Tactic.BvDecide.BitBlast.BoolExpr

open Std.Sat
open Lean.Elab.Tactic.BvDecide

def mkFalseCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkFalseCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval ofBoolExprCached (mkFalseCollapsible 1) AIG.mkAtomCached |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const false] -/
#guard_msgs in
#eval ofBoolExprCached (mkFalseCollapsible 16) AIG.mkAtomCached |>.aig.decls

def mkTrueCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const true
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and tree tree

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval ofBoolExprCached (mkTrueCollapsible 1) AIG.mkAtomCached |>.aig.decls

/-- info: #[Std.Sat.AIG.Decl.const true] -/
#guard_msgs in
#eval ofBoolExprCached (mkTrueCollapsible 16) AIG.mkAtomCached |>.aig.decls

def mkConstantCollapsible (n : Nat) : BoolExpr Nat :=
  match n with
  | 0 => .const false
  | n + 1 =>
    let tree := mkTrueCollapsible n
    .gate .and (.gate .and tree tree) (.const false)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := ofBoolExprCached (mkConstantCollapsible 1) AIG.mkAtomCached
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)

/-- info: (2, Std.Sat.AIG.Decl.const false) -/
#guard_msgs in
#eval
  let entry := ofBoolExprCached (mkConstantCollapsible 16) AIG.mkAtomCached
  (entry.aig.decls.size, entry.aig.decls[entry.ref.gate]!)
