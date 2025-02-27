import Lean.Elab.Command
import Lean.Elab.Open
/-!
Issue #2291

The following example would cause the pretty printer to panic.
-/

set_option trace.Compiler.simp true in
/--
info: [0]
---
info: [Compiler.simp] size: 22
    def _eval : Lean.MessageData :=
      let _x.1 := Lean.instToExprNat;
      let _x.2 := "Nat";
      let _x.3 := Lean.Name.mkStr1 _x.2;
      let _x.4 := @List.nil _;
      let type := Lean.Expr.const._override _x.3 _x.4;
      let _x.5 := "List";
      let _x.6 := "nil";
      let _x.7 := Lean.Name.mkStr2 _x.5 _x.6;
      let _x.8 := Lean.Level.zero._impl;
      let _x.9 := @List.nil _;
      let _x.10 := @List.cons _ _x.8 _x.9;
      let _x.11 := Lean.Expr.const._override _x.7 _x.10;
      let nil := Lean.Expr.app._override _x.11 type;
      let _x.12 := "cons";
      let _x.13 := Lean.Name.mkStr2 _x.5 _x.12;
      let _x.14 := Lean.Expr.const._override _x.13 _x.10;
      let cons := Lean.Expr.app._override _x.14 type;
      let _x.15 := 0;
      let _x.16 := @List.nil _;
      let _x.17 := @List.cons _ _x.15 _x.16;
      let _x.18 := @Lean.List.toExprAux.0 _ _x.1 nil cons _x.17;
      let _x.19 := Lean.MessageData.ofExpr _x.18;
      return _x.19
[Compiler.simp] size: 22
    def _eval : Lean.MessageData :=
      let _x.1 := Lean.instToExprNat;
      let _x.2 := "Nat";
      let _x.3 := Lean.Name.mkStr1 _x.2;
      let _x.4 := @List.nil _;
      let type := Lean.Expr.const._override _x.3 _x.4;
      let _x.5 := "List";
      let _x.6 := "nil";
      let _x.7 := Lean.Name.mkStr2 _x.5 _x.6;
      let _x.8 := Lean.Level.zero._impl;
      let _x.9 := @List.nil _;
      let _x.10 := @List.cons _ _x.8 _x.9;
      let _x.11 := Lean.Expr.const._override _x.7 _x.10;
      let nil := Lean.Expr.app._override _x.11 type;
      let _x.12 := "cons";
      let _x.13 := Lean.Name.mkStr2 _x.5 _x.12;
      let _x.14 := Lean.Expr.const._override _x.13 _x.10;
      let cons := Lean.Expr.app._override _x.14 type;
      let _x.15 := 0;
      let _x.16 := @List.nil _;
      let _x.17 := @List.cons _ _x.15 _x.16;
      let _x.18 := @Lean.List.toExprAux.0 _ _x.1 nil cons _x.17;
      let _x.19 := Lean.MessageData.ofExpr _x.18;
      return _x.19
[Compiler.simp] size: 6
    def _private.Lean.ToExpr.0.Lean.List.toExprAux._at_._eval.spec_0 nilFn consFn x.1 : Lean.Expr :=
      cases x.1 : Lean.Expr
      | List.nil =>
        return nilFn
      | List.cons head.2 tail.3 =>
        let _x.4 := Lean.mkNatLit head.2;
        let _x.5 := Lean.List.toExprAux._at_._eval.spec_0.0 nilFn consFn tail.3;
        let _x.6 := Lean.mkAppB consFn _x.4 _x.5;
        return _x.6
[Compiler.simp] size: 21
    def _eval : Lean.MessageData :=
      let _x.1 := "Nat";
      let _x.2 := Lean.Name.mkStr1 _x.1;
      let _x.3 := @List.nil _;
      let type := Lean.Expr.const._override _x.2 _x.3;
      let _x.4 := "List";
      let _x.5 := "nil";
      let _x.6 := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 := Lean.Level.zero._impl;
      let _x.8 := @List.nil _;
      let _x.9 := @List.cons _ _x.7 _x.8;
      let _x.10 := Lean.Expr.const._override _x.6 _x.9;
      let nil := Lean.Expr.app._override _x.10 type;
      let _x.11 := "cons";
      let _x.12 := Lean.Name.mkStr2 _x.4 _x.11;
      let _x.13 := Lean.Expr.const._override _x.12 _x.9;
      let cons := Lean.Expr.app._override _x.13 type;
      let _x.14 := 0;
      let _x.15 := @List.nil _;
      let _x.16 := @List.cons _ _x.14 _x.15;
      let _x.17 := Lean.List.toExprAux._at_._eval.spec_0.0 nil cons _x.16;
      let _x.18 := Lean.MessageData.ofExpr _x.17;
      return _x.18
[Compiler.simp] size: 6
    def _private.Lean.ToExpr.0.Lean.List.toExprAux._at_._eval.spec_0 nilFn consFn x.1 : Lean.Expr :=
      cases x.1 : Lean.Expr
      | List.nil =>
        return nilFn
      | List.cons head.2 tail.3 =>
        let _x.4 := Lean.mkNatLit head.2;
        let _x.5 := Lean.List.toExprAux._at_._eval.spec_0.0 nilFn consFn tail.3;
        let _x.6 := Lean.mkAppB consFn _x.4 _x.5;
        return _x.6
[Compiler.simp] size: 20
    def _eval : Lean.MessageData :=
      let _x.1 := "Nat";
      let _x.2 := Lean.Name.mkStr1 _x.1;
      let _x.3 := [] _;
      let type := Lean.Expr.const._override _x.2 _x.3;
      let _x.4 := "List";
      let _x.5 := "nil";
      let _x.6 := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 := Lean.Level.zero._impl;
      let _x.8 := List.cons _ _x.7 _x.3;
      let _x.9 := Lean.Expr.const._override _x.6 _x.8;
      let nil := Lean.Expr.app._override _x.9 type;
      let _x.10 := "cons";
      let _x.11 := Lean.Name.mkStr2 _x.4 _x.10;
      let _x.12 := Lean.Expr.const._override _x.11 _x.8;
      let cons := Lean.Expr.app._override _x.12 type;
      let _x.13 := 0;
      let _x.14 := [] _;
      let _x.15 := List.cons _ _x.13 _x.14;
      let _x.16 := Lean.List.toExprAux._at_._eval.spec_0.0 nil cons _x.15;
      let _x.17 := Lean.MessageData.ofExpr _x.16;
      return _x.17
[Compiler.simp] size: 6
    def _private.Lean.ToExpr.0.Lean.List.toExprAux._at_._eval.spec_0 nilFn consFn x.1 : Lean.Expr :=
      cases x.1 : Lean.Expr
      | List.nil =>
        return nilFn
      | List.cons head.2 tail.3 =>
        let _x.4 := Lean.mkNatLit head.2;
        let _x.5 := Lean.List.toExprAux._at_._eval.spec_0.0 nilFn consFn tail.3;
        let _x.6 := Lean.mkAppB consFn _x.4 _x.5;
        return _x.6
[Compiler.simp] size: 20
    def _eval : Lean.MessageData :=
      let _x.1 := "Nat";
      let _x.2 := Lean.Name.mkStr1 _x.1;
      let _x.3 := [] _;
      let type := Lean.Expr.const._override _x.2 _x.3;
      let _x.4 := "List";
      let _x.5 := "nil";
      let _x.6 := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 := Lean.Level.zero._impl;
      let _x.8 := List.cons _ _x.7 _x.3;
      let _x.9 := Lean.Expr.const._override _x.6 _x.8;
      let nil := Lean.Expr.app._override _x.9 type;
      let _x.10 := "cons";
      let _x.11 := Lean.Name.mkStr2 _x.4 _x.10;
      let _x.12 := Lean.Expr.const._override _x.11 _x.8;
      let cons := Lean.Expr.app._override _x.12 type;
      let _x.13 := 0;
      let _x.14 := [] _;
      let _x.15 := List.cons _ _x.13 _x.14;
      let _x.16 := Lean.List.toExprAux._at_._eval.spec_0.0 nil cons _x.15;
      let _x.17 := Lean.MessageData.ofExpr _x.16;
      return _x.17
[Compiler.simp] size: 6
    def _private.Lean.ToExpr.0.Lean.List.toExprAux._at_._eval.spec_0 nilFn consFn x.1 : Lean.Expr :=
      cases x.1 : Lean.Expr
      | List.nil =>
        return nilFn
      | List.cons head.2 tail.3 =>
        let _x.4 := Lean.mkNatLit head.2;
        let _x.5 := Lean.List.toExprAux._at_._eval.spec_0.0 nilFn consFn tail.3;
        let _x.6 := Lean.mkAppB consFn _x.4 _x.5;
        return _x.6
[Compiler.simp] size: 20
    def _eval : Lean.MessageData :=
      let _x.1 := "Nat";
      let _x.2 := Lean.Name.mkStr1 _x.1;
      let _x.3 := [] _;
      let type := Lean.Expr.const._override _x.2 _x.3;
      let _x.4 := "List";
      let _x.5 := "nil";
      let _x.6 := Lean.Name.mkStr2 _x.4 _x.5;
      let _x.7 := Lean.Level.zero._impl;
      let _x.8 := List.cons _ _x.7 _x.3;
      let _x.9 := Lean.Expr.const._override _x.6 _x.8;
      let nil := Lean.Expr.app._override _x.9 type;
      let _x.10 := "cons";
      let _x.11 := Lean.Name.mkStr2 _x.4 _x.10;
      let _x.12 := Lean.Expr.const._override _x.11 _x.8;
      let cons := Lean.Expr.app._override _x.12 type;
      let _x.13 := 0;
      let _x.14 := [] _;
      let _x.15 := List.cons _ _x.13 _x.14;
      let _x.16 := Lean.List.toExprAux._at_._eval.spec_0.0 nil cons _x.15;
      let _x.17 := Lean.MessageData.ofExpr _x.16;
      return _x.17
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
