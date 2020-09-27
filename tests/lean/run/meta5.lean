import Lean.Meta
new_frontend
open Lean
open Lean.Meta

def tst1 : MetaM Unit :=
withLocalDeclD `y (mkConst `Nat) $ fun y => do
withLetDecl `x (mkConst `Nat) (mkNatLit 0) $ fun x => do {
  let mvar ← mkFreshExprMVar (mkConst `Nat) MetavarKind.syntheticOpaque;
  trace! `Meta mvar;
  let r ← mkLambdaFVars #[y, x] mvar;
  trace! `Meta r;
  let v := mkApp2 (mkConst `Nat.add) x y;
  assignExprMVar mvar.mvarId! v;
  trace! `Meta mvar;
  trace! `Meta r;
  let mctx ← getMCtx;
  mctx.decls.forM $ fun mvarId mvarDecl => do {
    trace! `Meta ("?" ++ mvarId ++ " : " ++ mvarDecl.type);
    pure ()
  };
  pure ()
}

set_option trace.Meta true

#eval tst1
