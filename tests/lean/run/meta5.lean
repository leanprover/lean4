import Lean.Meta

open Lean
open Lean.Meta

def tst1 : MetaM Unit :=
withLocalDeclD `y (mkConst `Nat) $ fun y => do
withLetDecl `x (mkConst `Nat) (mkNatLit 0) $ fun x => do {
  let mvar ← mkFreshExprMVar (mkConst `Nat) MetavarKind.syntheticOpaque;
  trace[Meta.debug] mvar;
  let r ← mkLambdaFVars #[y, x] mvar;
  trace[Meta.debug] r;
  let v := mkApp2 (mkConst `Nat.add) x y;
  mvar.mvarId!.assign v;
  trace[Meta.debug] mvar;
  trace[Meta.debug] r;

  let mctx ← getMCtx;
  let sortedDecls := mctx.decls.toArray.qsort (fun ⟨v1, _⟩ ⟨v2, _⟩ => v1.name.lt v2.name);
  let mut i : Nat := 0;
  for ⟨_, mvarDecl⟩ in sortedDecls do
    trace[Meta.debug] m!"?{i} : {mvarDecl.type}";
    i := i + 1;
}

set_option pp.mvars false
set_option trace.Meta.debug true

/--
info: [Meta.debug] ?_
[Meta.debug] fun y =>
      let x := 0;
      ?_
[Meta.debug] x.add y
[Meta.debug] fun y =>
      let x := 0;
      x.add y
[Meta.debug] ?0 : Nat
[Meta.debug] ?1 : Nat → Nat → Nat
-/
#guard_msgs in
#eval tst1
