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

@[inline] def Expr.heq? (p : Expr) : Option (Expr × Expr × Expr × Expr) :=
if p.isAppOfArity `HEq 4 then
  some (p.getArg! 0, p.getArg! 1, p.getArg! 2, p.getArg! 4)
else
  none

@[inline] def Expr.arrow? : Expr → Option (Expr × Expr)
| Expr.forallE _ α β _ => if β.hasLooseBVars then none else some (α, β)
| _                    => none

namespace Meta

def mkEq (a b : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   pure $ mkApp3 (mkConst `Eq [u]) aType a b

def mkHEq (a b : Expr) : MetaM Expr :=
do aType ← inferType a;
   bType ← inferType b;
   u ← getLevel aType;
   pure $ mkApp4 (mkConst `HEq [u]) aType a bType b

def mkEqRefl (a : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   pure $ mkApp2 (mkConst `Eq.refl [u]) aType a

def mkHEqRefl (a : Expr) : MetaM Expr :=
do aType ← inferType a;
   u ← getLevel aType;
   pure $ mkApp2 (mkConst `HEq.refl [u]) aType a

private def infer (h : Expr) : MetaM Expr :=
do hType ← inferType h;
   whnfD hType

def mkEqSymm (h : Expr) : MetaM Expr :=
if h.isAppOf `Eq.refl then pure h
else do
  hType ← infer h;
  match hType.eq? with
  | some (α, a, b) => do u ← getLevel α; pure $ mkApp4 (mkConst `Eq.symm [u]) α a b h
  | none => throwEx $ Exception.appBuilder `Eq.symm #[h]

def mkEqTrans (h₁ h₂ : Expr) : MetaM Expr :=
if h₁.isAppOf `Eq.refl then pure h₂
else if h₂.isAppOf `Eq.refl then pure h₁
else do
  hType₁ ← infer h₁;
  hType₂ ← infer h₂;
  match hType₁.eq?, hType₂.eq? with
  | some (α, a, b), some (_, _, c) =>
    do u ← getLevel α; pure $ mkApp6 (mkConst `Eq.trans [u]) α a b c h₁ h₂
  | _, _ => throwEx $ Exception.appBuilder `Eq.trans #[h₁, h₂]

def mkHEqSymm (h : Expr) : MetaM Expr :=
if h.isAppOf `HEq.refl then pure h
else do
  hType ← infer h;
  match hType.heq? with
  | some (α, a, β, b) => do u ← getLevel α; pure $ mkApp5 (mkConst `HEq.symm [u]) α β a b h
  | none => throwEx $ Exception.appBuilder `HEq.symm #[h]

def mkHEqTrans (h₁ h₂ : Expr) : MetaM Expr :=
if h₁.isAppOf `HEq.refl then pure h₂
else if h₂.isAppOf `HEq.refl then pure h₁
else do
  hType₁ ← infer h₁;
  hType₂ ← infer h₂;
  match hType₁.heq?, hType₂.heq? with
  | some (α, a, β, b), some (_, _, γ, c) => do
    u ← getLevel α; pure $ mkApp8 (mkConst `HEq.trans [u]) α β γ a b c h₁ h₂
  | _, _ => throwEx $ Exception.appBuilder `HEq.trans #[h₁, h₂]

def mkCongrArg (f h : Expr) : MetaM Expr :=
do hType ← infer h;
   fType ← infer f;
   match fType.arrow?, hType.eq? with
   | some (α, β), some (_, a, b) => do
     u ← getLevel α; v ← getLevel β; pure $ mkApp6 (mkConst `congrArg [u, v]) α β a b f h
   | _, _ => throwEx $ Exception.appBuilder `congrArg #[f, h]

def mkCongrFun (h a : Expr) : MetaM Expr :=
do hType ← infer h;
   match hType.eq? with
   | some (ρ, f, g) => do
     ρ ← whnfD ρ;
     match ρ with
     | Expr.forallE n α β _ => do
       let β' := Lean.mkLambda n BinderInfo.default α β;
       u ← getLevel α;
       v ← getLevel (mkApp β' a);
       pure $ mkApp6 (mkConst `congrFun [u, v]) α β' f g h a
     | _ => throwEx $ Exception.appBuilder `congrFun #[h, a]
   | _ => throwEx $ Exception.appBuilder `congrFun #[h, a]

def mkCongr (h₁ h₂ : Expr) : MetaM Expr :=
do hType₁ ← infer h₁;
   hType₂ ← infer h₂;
   match hType₁.eq?, hType₂.eq? with
   | some (ρ, f, g), some (α, a, b) => do
     ρ ← whnfD ρ;
     match ρ.arrow? with
     | some (_, β) => do
       u ← getLevel α;
       v ← getLevel β;
       pure $ mkApp8 (mkConst `congr [u, v]) α β f g a b h₁ h₂
     | _ => throwEx $ Exception.appBuilder `congr #[h₁, h₂]
   | _, _ => throwEx $ Exception.appBuilder `congr #[h₁, h₂]

@[inline] def withAppBuilder {α} (x : MetaM α) : MetaM α :=
traceCtx `Meta.appBuilder x

end Meta
end Lean
