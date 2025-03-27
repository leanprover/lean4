import Lean.Elab.Command
import Lean.Elab.Open
/-!
Issue #2291

The following example would cause the pretty printer to panic.
-/

set_option trace.compiler.simp true in
/--
info: [0]
---
info: [compiler.simp] >> _eval
let _x_21 := `Nat;
let _x_22 := [];
let _x_23 := Lean.Expr.const _x_21 _x_22;
let _x_24 := `List.nil;
let _x_25 := Lean.Level.zero :: _x_22;
let _x_26 := Lean.Expr.const _x_24 _x_25;
let _x_27 := _x_26.app _x_23;
let _x_28 := `List.cons;
let _x_29 := Lean.Expr.const _x_28 _x_25;
let _x_30 := _x_29.app _x_23;
let _x_31 := [];
let _x_32 := 0 :: _x_31;
let _x_33 := Lean.List.toExprAux✝ _x_27 _x_30 _x_32;
Lean.MessageData.ofExpr _x_33
[compiler.simp] >> _private.Lean.ToExpr.0.Lean.List.toExprAux._at._eval._spec_1
fun nilFn consFn x =>
  List.casesOn fun head tail =>
    let _x_1 := Lean.mkNatLit head;
    let _x_2 := Lean.List.toExprAux._at._eval._spec_1✝ nilFn consFn tail;
    Lean.mkAppB consFn _x_1 _x_2
>> _eval
let _x_14 := Lean.Name.str._override Lean.Name.anonymous._impl "Nat";
let _x_15 := List.nil _neutral;
let _x_16 := Lean.Expr.const._override _x_14 _x_15;
let _x_17 := `List.nil;
let _x_18 := List.cons _neutral Lean.Level.zero._impl _x_15;
let _x_19 := Lean.Expr.const._override _x_17 _x_18;
let _x_20 := Lean.Expr.app._override _x_19 _x_16;
let _x_21 := `List.cons;
let _x_22 := Lean.Expr.const._override _x_21 _x_18;
let _x_23 := Lean.Expr.app._override _x_22 _x_16;
let _x_24 := List.cons _neutral 0 _x_15;
let _x_25 := Lean.List.toExprAux._at._eval._spec_1✝ _x_20 _x_23 _x_24;
Lean.MessageData.ofExpr _x_25
[compiler.simp] >> _private.Lean.ToExpr.0.Lean.List.toExprAux._at._eval._spec_1
fun nilFn consFn x =>
  List.casesOn fun head tail =>
    let _x_1 := Lean.mkNatLit head;
    let _x_2 := Lean.List.toExprAux._at._eval._spec_1✝ nilFn consFn tail;
    Lean.mkAppB consFn _x_1 _x_2
>> _eval
let _x_1 := Lean.Name.str._override Lean.Name.anonymous._impl "Nat";
let _x_2 := List.nil _neutral;
let _x_3 := Lean.Expr.const._override _x_1 _x_2;
let _x_4 := `List.nil;
let _x_5 := List.cons _neutral Lean.Level.zero._impl _x_2;
let _x_6 := Lean.Expr.const._override _x_4 _x_5;
let _x_7 := Lean.Expr.app._override _x_6 _x_3;
let _x_8 := `List.cons;
let _x_9 := Lean.Expr.const._override _x_8 _x_5;
let _x_10 := Lean.Expr.app._override _x_9 _x_3;
let _x_11 := List.cons _neutral 0 _x_2;
let _x_12 := Lean.List.toExprAux._at._eval._spec_1✝ _x_7 _x_10 _x_11;
Lean.MessageData.ofExpr _x_12
[compiler.simp] >> _private.Lean.ToExpr.0.Lean.List.toExprAux._at._eval._spec_1
fun nilFn consFn x =>
  List.casesOn fun head tail =>
    let _x_1 := Lean.mkNatLit head;
    let _x_2 := Lean.List.toExprAux._at._eval._spec_1✝ nilFn consFn tail;
    Lean.mkAppB consFn _x_1 _x_2
>> _eval._closed_1
"Nat"
>> _eval._closed_2
Lean.Name.str._override Lean.Name.anonymous._impl _eval._closed_1
>> _eval._closed_3
let _x_1 := List.nil _neutral;
Lean.Expr.const._override _eval._closed_2 _x_1
>> _eval._closed_4
"List"
>> _eval._closed_5
"nil"
>> _eval._closed_6
Lean.Name.mkStr2 _eval._closed_4 _eval._closed_5
>> _eval._closed_7
let _x_1 := List.nil _neutral;
List.cons _neutral Lean.Level.zero._impl _x_1
>> _eval._closed_8
Lean.Expr.const._override _eval._closed_6 _eval._closed_7
>> _eval._closed_9
Lean.Expr.app._override _eval._closed_8 _eval._closed_3
>> _eval._closed_10
"cons"
>> _eval._closed_11
Lean.Name.mkStr2 _eval._closed_4 _eval._closed_10
>> _eval._closed_12
Lean.Expr.const._override _eval._closed_11 _eval._closed_7
>> _eval._closed_13
Lean.Expr.app._override _eval._closed_12 _eval._closed_3
>> _eval._closed_14
let _x_1 := List.nil _neutral;
List.cons _neutral 0 _x_1
>> _eval
let _x_1 :=
  Lean.List.toExprAux._at._eval._spec_1✝ _eval._closed_9 _eval._closed_13
    _eval._closed_14;
Lean.MessageData.ofExpr _x_1
-/
#guard_msgs in
#eval [0]


/-!
Fixing the above involved changing `Lean.unresolveNameGlobal`.
Here, we also verify that we do not pretty print using any aliases that have macro scopes.
-/

open Lean in
elab "add_bad_alias " n:ident : command => withFreshMacroScope do
  let declName ← Elab.OpenDecl.resolveNameUsingNamespaces [← getCurrNamespace] n
  let badName ← MonadQuotation.addMacroScope `bad
  modify fun s => { s with env := addAlias s.env badName declName }

def f := 1

add_bad_alias f

-- Formerly was info: bad✝ : ℕ
/-- info: f : Nat -/
#guard_msgs in #check (f)
