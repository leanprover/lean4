/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Basic tests for the custom first-order unifier used by tabled
typeclass resolution.
-/
import init.lean init.lean.typeclass.context

open Lean
open Lean.TypeClass
open Lean.TypeClass.Context

def testEUnify1 : EState String Context Expr := do
t ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify (mkApp (mkConst "f") [mkConst "a"]) t;
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t

def testEUnify2 : EState String Context Expr := do
t ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify (mkApp (mkConst "f") [mkConst "a"]) (mkApp (mkConst "f") [t]);
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t

def testEUnify3 : EState String Context Expr := do
t ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify t t;
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t

def testEUnify4 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify (Expr.pi "foo" BinderInfo.default t₂ t₁) (Expr.pi "foo" BinderInfo.default t₁ t₂);
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t₂

def testEUnify5 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify (Expr.pi "foo" BinderInfo.default t₁ t₂) (Expr.pi "foo" BinderInfo.default t₂ t₁);
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t₂

def testEUnify6 : EState String Context Expr := do
(u, ctx) ← get >>= λ ctx => pure $ Context.uNewMeta.run ctx;
set ctx;
let t₁ := Expr.const "foo" [Level.zero];
let t₂ := Expr.const "foo" [u];
eUnify t₁ t₂;
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t₂

def testEUnify7 : EState String Context Expr := do
(e, ctx) ← get >>= λ ctx => pure $ (Context.eNewMeta $ Expr.sort Level.zero).run ctx;
set ctx;
let t₁ := Expr.fvar "foo";
let t₂ := e;
eUnify t₁ t₂;
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t₂

def testEAssign1 : EState String Context Expr := do
t ← EState.fromState $ eNewMeta (mkConst "Term");
EState.fromState $ eAssign t $ mkApp (mkConst "f") [mkConst "a"];
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t

def testClash1 : EState String Context Expr := do
eUnify (mkConst "f") (mkConst "g");
pure $ default _

def testClash2 : EState String Context Expr := do
eUnify (mkApp (mkConst "f") [mkConst "a"]) (mkApp (mkConst "g") [mkConst "a"]);
pure $ default _

def testClash3 : EState String Context Expr := do
eUnify (mkApp (mkConst "f") [mkConst "a"]) (mkApp (mkConst "f") [mkConst "b"]);
pure $ default _

def testClash4 : EState String Context Expr := do
eUnify (mkApp (mkConst "f") [mkConst "a"]) (mkApp (mkConst "f") []);
pure $ default _

def testChain1 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
eUnify t₁ t₂;
eUnify t₂ $ mkConst "foo";
get >>= λ (ctx : Context) => pure $ ctx.eInstantiate t₁

def testAlphaNorm1 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
pure $ αNorm $ mkApp (mkConst "f") [t₁, t₂]

def testAlphaNorm2 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
pure $ αNorm $ mkApp (mkConst "f") [t₂, t₁]

def testAlphaNorm3 : EState String Context Expr := do
pure $ αNorm (mkConst "f")

def testAlphaNorm4 : EState String Context Expr := do
t₁ ← EState.fromState $ eNewMeta (mkConst "Term");
t₂ ← EState.fromState $ eNewMeta (mkConst "Term");
pure $ αNorm $ Expr.pi "foo" BinderInfo.default (mkApp (mkConst "f") [t₂]) (mkApp (mkConst "g") [t₁])

#eval testEUnify1.run {}
#eval testEUnify2.run {}
#eval testEUnify3.run {}
#eval testEUnify4.run {}
#eval testEUnify5.run {}
#eval testEUnify6.run {}
#eval testEUnify7.run {}
#eval testEAssign1.run {}
#eval testClash1.run {}
#eval testClash2.run {}
#eval testClash3.run {}
#eval testClash4.run {}
#eval testChain1.run {}
#eval testAlphaNorm1.run {}
#eval testAlphaNorm2.run {}
#eval testAlphaNorm3.run {}
#eval testAlphaNorm4.run {}
