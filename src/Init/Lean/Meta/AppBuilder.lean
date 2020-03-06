/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Lean.Meta.SynthInstance

namespace Lean

@[inline] def Expr.eq? (p : Expr) : Option (Expr × Expr × Expr) :=
if p.isAppOfArity `Eq 3 then
  some (p.getArg! 0, p.getArg! 1, p.getArg! 2)
else
  none

@[inline] def Expr.iff? (p : Expr) : Option (Expr × Expr) :=
if p.isAppOfArity `Iff 2 then
  some (p.getArg! 0, p.getArg! 1)
else
  none

@[inline] def Expr.heq? (p : Expr) : Option (Expr × Expr × Expr × Expr) :=
if p.isAppOfArity `HEq 4 then
  some (p.getArg! 0, p.getArg! 1, p.getArg! 2, p.getArg! 4)
else
  none

@[inline] def Expr.arrow? : Expr → Option (Expr × Expr)
| Expr.forallE _ α β _ => if β.hasLooseBVars then none else some (α, β)
| _                    => none

namespace Meta

def mkEq (a b : Expr) : MetaM Expr := do
aType ← inferType a;
u ← getLevel aType;
pure $ mkApp3 (mkConst `Eq [u]) aType a b

def mkHEq (a b : Expr) : MetaM Expr := do
aType ← inferType a;
bType ← inferType b;
u ← getLevel aType;
pure $ mkApp4 (mkConst `HEq [u]) aType a bType b

def mkEqRefl (a : Expr) : MetaM Expr := do
aType ← inferType a;
u ← getLevel aType;
pure $ mkApp2 (mkConst `Eq.refl [u]) aType a

def mkHEqRefl (a : Expr) : MetaM Expr := do
aType ← inferType a;
u ← getLevel aType;
pure $ mkApp2 (mkConst `HEq.refl [u]) aType a

private def infer (h : Expr) : MetaM Expr := do
hType ← inferType h;
whnfD hType

def mkEqSymm (h : Expr) : MetaM Expr :=
if h.isAppOf `Eq.refl then pure h
else do
  hType ← infer h;
  match hType.eq? with
  | some (α, a, b) => do u ← getLevel α; pure $ mkApp4 (mkConst `Eq.symm [u]) α a b h
  | none => throwEx $ Exception.appBuilder `Eq.symm "equality proof expected" #[h]

def mkEqTrans (h₁ h₂ : Expr) : MetaM Expr :=
if h₁.isAppOf `Eq.refl then pure h₂
else if h₂.isAppOf `Eq.refl then pure h₁
else do
  hType₁ ← infer h₁;
  hType₂ ← infer h₂;
  match hType₁.eq?, hType₂.eq? with
  | some (α, a, b), some (_, _, c) =>
    do u ← getLevel α; pure $ mkApp6 (mkConst `Eq.trans [u]) α a b c h₁ h₂
  | _, _ => throwEx $ Exception.appBuilder `Eq.trans "equality proof expected" #[h₁, h₂]

def mkHEqSymm (h : Expr) : MetaM Expr :=
if h.isAppOf `HEq.refl then pure h
else do
  hType ← infer h;
  match hType.heq? with
  | some (α, a, β, b) => do u ← getLevel α; pure $ mkApp5 (mkConst `HEq.symm [u]) α β a b h
  | none => throwEx $ Exception.appBuilder `HEq.symm "heterogeneous equality proof expected" #[h]

def mkHEqTrans (h₁ h₂ : Expr) : MetaM Expr :=
if h₁.isAppOf `HEq.refl then pure h₂
else if h₂.isAppOf `HEq.refl then pure h₁
else do
  hType₁ ← infer h₁;
  hType₂ ← infer h₂;
  match hType₁.heq?, hType₂.heq? with
  | some (α, a, β, b), some (_, _, γ, c) => do
    u ← getLevel α; pure $ mkApp8 (mkConst `HEq.trans [u]) α β γ a b c h₁ h₂
  | _, _ => throwEx $ Exception.appBuilder `HEq.trans "heterogeneous equality proof expected" #[h₁, h₂]

def mkEqOfHEq (h : Expr) : MetaM Expr := do
hType ← infer h;
match hType.heq? with
| some (α, a, β, b) => do
  unlessM (isDefEq α β) $ throwEx $ Exception.appBuilder `eqOfHEq "heterogeneous equality types are not definitionally equal" #[α, β];
  u ← getLevel α;
  pure $ mkApp4 (mkConst `eqOfHEq [u]) α a b h
| _ =>
  throwEx $ Exception.appBuilder `HEq.trans "heterogeneous equality proof expected" #[h]

def mkCongrArg (f h : Expr) : MetaM Expr := do
hType ← infer h;
fType ← infer f;
match fType.arrow?, hType.eq? with
| some (α, β), some (_, a, b) => do
  u ← getLevel α; v ← getLevel β; pure $ mkApp6 (mkConst `congrArg [u, v]) α β a b f h
| none, _ => throwEx $ Exception.appBuilder `congrArg "non-dependent function expected" #[f, h]
| _, none => throwEx $ Exception.appBuilder `congrArg "equality proof expected" #[f, h]

def mkCongrFun (h a : Expr) : MetaM Expr := do
hType ← infer h;
match hType.eq? with
| some (ρ, f, g) => do
  ρ ← whnfD ρ;
  match ρ with
  | Expr.forallE n α β _ => do
    let β' := Lean.mkLambda n BinderInfo.default α β;
    u ← getLevel α;
    v ← getLevel (mkApp β' a);
    pure $ mkApp6 (mkConst `congrFun [u, v]) α β' f g h a
  | _ => throwEx $ Exception.appBuilder `congrFun "equality proof between functions expected" #[h, a]
| _ => throwEx $ Exception.appBuilder `congrFun "equality proof expected" #[h, a]

def mkCongr (h₁ h₂ : Expr) : MetaM Expr := do
hType₁ ← infer h₁;
hType₂ ← infer h₂;
match hType₁.eq?, hType₂.eq? with
| some (ρ, f, g), some (α, a, b) => do
  ρ ← whnfD ρ;
  match ρ.arrow? with
  | some (_, β) => do
    u ← getLevel α;
    v ← getLevel β;
    pure $ mkApp8 (mkConst `congr [u, v]) α β f g a b h₁ h₂
  | _ => throwEx $ Exception.appBuilder `congr "non-dependent function expected" #[h₁, h₂]
| _, _ => throwEx $ Exception.appBuilder `congr "equality proof expected" #[h₁, h₂]

private def mkAppMFinal (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
instMVars.forM $ fun mvarId => do {
  mvarDecl ← getMVarDecl mvarId;
  mvarVal  ← synthInstance mvarDecl.type;
  assignExprMVar mvarId mvarVal
};
result ← instantiateMVars (mkAppN f args);
whenM (hasAssignableMVar result) $ throwEx $ Exception.appBuilder `mkAppM "result contains metavariables" #[result];
pure result

private partial def mkAppMAux (f : Expr) (xs : Array Expr) : Nat → Array Expr → Nat → Array MVarId → Expr → MetaM Expr
| i, args, j, instMVars, Expr.forallE n d b c => do
  let d  := d.instantiateRevRange j args.size args;
  match c.binderInfo with
  | BinderInfo.implicit     => do mvar ← mkFreshExprMVar d n; mkAppMAux i (args.push mvar) j instMVars b
  | BinderInfo.instImplicit => do mvar ← mkFreshExprMVar d n MetavarKind.synthetic; mkAppMAux i (args.push mvar) j (instMVars.push mvar.mvarId!) b
  | _ =>
    if h : i < xs.size then do
      let x := xs.get ⟨i, h⟩;
      xType ← inferType x;
      condM (isDefEq d xType)
        (mkAppMAux (i+1) (args.push x) j instMVars b)
        (throwEx $ Exception.appTypeMismatch (mkAppN f args) x)
    else
      mkAppMFinal f args instMVars
| i, args, j, instMVars, type => do
  let type := type.instantiateRevRange j args.size args;
  type ← whnfD type;
  if type.isForall then
    mkAppMAux i args args.size instMVars type
  else if i == xs.size then
    mkAppMFinal f args instMVars
  else
    throwEx $ Exception.appBuilder `mkAppM "too many explicit arguments provided" (#[f] ++ xs)

def mkAppM (constName : Name) (xs : Array Expr) : MetaM Expr :=
traceCtx `Meta.appBuilder $ withNewMCtxDepth $ do
  cinfo ← getConstInfo constName;
  us ← cinfo.lparams.mapM $ fun _ => mkFreshLevelMVar;
  let f := mkConst constName us;
  let fType := cinfo.instantiateTypeLevelParams us;
  mkAppMAux f xs 0 #[] 0 #[] fType

def mkEqNDRec (motive h1 h2 : Expr) : MetaM Expr :=
if h2.isAppOf `Eq.refl then pure h1
else do
  h2Type ← infer h2;
  match h2Type.eq? with
  | none => throwEx $ Exception.appBuilder `Eq.ndrec "equality proof expected" #[h2]
  | some (α, a, b) => do
    u2 ← getLevel α;
    motiveType ← infer motive;
    match motiveType with
    | Expr.forallE _ _ (Expr.sort u1 _) _ =>
      pure $ mkAppN (mkConst `Eq.ndrec [u1, u2]) #[α, a, motive, h1, b, h2]
    | _ => throwEx $ Exception.appBuilder `Eq.ndrec "invalid motive" #[motive]

def mkEqRec (motive h1 h2 : Expr) : MetaM Expr :=
if h2.isAppOf `Eq.refl then pure h1
else do
  h2Type ← infer h2;
  match h2Type.eq? with
  | none => throwEx $ Exception.appBuilder `Eq.rec "equality proof expected" #[h2]
  | some (α, a, b) => do
    u2 ← getLevel α;
    motiveType ← infer motive;
    match motiveType with
    | Expr.forallE _ _ (Expr.forallE _ _ (Expr.sort u1 _) _) _ =>
      pure $ mkAppN (mkConst `Eq.rec [u1, u2]) #[α, a, motive, h1, b, h2]
    | _ => throwEx $ Exception.appBuilder `Eq.rec "invalid motive" #[motive]

def mkEqMP (eqProof pr : Expr) : MetaM Expr :=
mkAppM `Eq.mp #[eqProof, pr]

def mkEqMPR (eqProof pr : Expr) : MetaM Expr :=
mkAppM `Eq.mpr #[eqProof, pr]

end Meta
end Lean
