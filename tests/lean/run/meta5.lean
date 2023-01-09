import Lean

open Lean
open Lean.Meta

def tst1 : MetaM Unit :=
withLocalDeclD `y (mkConst `Nat) $ fun y => do
withLetDecl `x (mkConst `Nat) (mkNatLit 0) $ fun x => do {
  let mvar ← mkFreshExprMVar (mkConst `Nat) MetavarKind.syntheticOpaque;
  trace[Meta.debug] mvar;
  let r ← mkLambdaFVars #[y, x] mvar;
  trace[Message.debug] r;
  let v := mkApp2 (mkConst `Nat.add) x y;
  assignExprMVar mvar.mvarId! v;
  trace[Meta.debug] mvar;
  trace[Meta.debug] r;
  let mctx ← getMCtx;
  mctx.decls.forM fun mvarId mvarDecl => do
    trace[Meta.debug] m!"?{mvarId.name} : {mvarDecl.type}"
}

set_option trace.Meta.debug true

#eval tst1
