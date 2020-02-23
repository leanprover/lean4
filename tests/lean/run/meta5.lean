import Init.Lean.Meta
open Lean
open Lean.Meta

def tst1 : MetaM Unit :=
withLocalDecl `y (mkConst `Nat) BinderInfo.default $ fun y => do
withLetDecl `x (mkConst `Nat) (mkNatLit 0) $ fun x => do {
  mvar ← mkFreshExprMVar (mkConst `Nat) Name.anonymous MetavarKind.syntheticOpaque;
  trace! `Meta mvar;
  r ← mkLambda #[y, x] mvar;
  trace! `Meta r;
  let v := mkApp2 (mkConst `Nat.add) x y;
  assignExprMVar mvar.mvarId! v;
  trace! `Meta mvar;
  trace! `Meta r;
  mctx ← getMCtx;
  mctx.decls.forM $ fun mvarId mvarDecl => do {
    trace! `Meta ("?" ++ mvarId ++ " : " ++ mvarDecl.type);
    pure ()
  };
  pure ()
}

set_option trace.Meta true

#eval tst1
