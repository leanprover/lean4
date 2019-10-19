/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Custom unifier for tabled typeclass resolution.

Note: this file will be removed once the unifier is implemented in Lean.
-/
prelude
import Init.Data.PersistentArray
import Init.Lean.Expr
import Init.Lean.MetavarContext

namespace Lean
namespace TypeClass

structure Context : Type :=
(uVals  : PersistentArray (Option Level) := PersistentArray.empty)
(eTypes : PersistentArray Expr           := PersistentArray.empty)
(eVals  : PersistentArray (Option Expr)  := PersistentArray.empty)

instance Context.Inhabited : Inhabited Context := ⟨{}⟩

structure ContextFail : Type :=
(msg : String)

abbrev ContextFn : Type → Type := EState ContextFail Context

namespace Context

def metaPrefix : Name :=
mkSimpleName "_tc_meta"

def alphaMetaPrefix : Name :=
mkSimpleName "_tc_alpha"

-- Expressions

def eMetaIdx : Expr → Option Nat
| Expr.mvar (Name.mkNumeral n idx) => guard (n == metaPrefix) *> pure idx
| _ => none

def eIsMeta (e : Expr) : Bool := (eMetaIdx e).toBool

def eNewMeta (type : Expr) : State Context Expr :=
do ctx ← get;
   let idx := ctx.eTypes.size;
   set { eTypes := ctx.eTypes.push type, eVals := ctx.eVals.push none, .. ctx };
   pure $ Expr.mvar (mkNumName metaPrefix idx)

def eLookupIdx (idx : Nat) : State Context (Option Expr) :=
do ctx ← get; pure $ ctx.eVals.get! idx

partial def eShallowInstantiate (e : Expr) : State Context Expr :=
match eMetaIdx e with
| some idx => get >>= λ ctx =>
  match ctx.eVals.get! idx with
  | none => pure e
  | some v => pure v
| none => pure e

def eInferIdx (idx : Nat) : State Context Expr :=
do ctx ← get; pure $ ctx.eTypes.get! idx

def eInfer (ctx : Context) (mvar : Expr) : Expr :=
match eMetaIdx mvar with
| some idx => ctx.eTypes.get! idx
| none     => panic! "eInfer called on non-(tmp-)mvar"

def eAssignIdx (idx : Nat) (e : Expr) : State Context Unit :=
modify $ λ ctx => { eVals := ctx.eVals.set idx (some e) .. ctx }

def eAssign (mvar : Expr) (e : Expr) : State Context Unit :=
match eMetaIdx mvar with
| some idx => modify $ λ ctx => { eVals := ctx.eVals.set idx (some e) .. ctx }
| _        => panic! "eAssign called on non-(tmp-)mvar"

partial def eFind (f : Expr → Bool) : Expr → Bool
| e =>
  if f e
  then true
  else
    match e with
    | Expr.app f a => eFind f || eFind a
    | Expr.pi _ _ d b => eFind d || eFind b
    | _ => false

def eOccursIn (t₀ : Expr) (e : Expr) : Bool :=
eFind (λ t => t == t₀) e

def eHasETmpMVar (e : Expr) : Bool :=
eFind eIsMeta e

-- Levels

def uMetaIdx : Level → Option Nat
| Level.mvar (Name.mkNumeral n idx) => guard (n == metaPrefix) *> pure idx
| _ => none

def uIsMeta (l : Level) : Bool := (uMetaIdx l).toBool

def uNewMeta : State Context Level :=
do ctx ← get;
   let idx := ctx.uVals.size;
   set { uVals := ctx.uVals.push none, .. ctx };
   pure $ Level.mvar (mkNumName metaPrefix idx)

def uLookupIdx (idx : Nat) : State Context (Option Level) :=
do ctx ← get; pure $ ctx.uVals.get! idx

partial def uShallowInstantiate (l : Level) : State Context Level :=
match uMetaIdx l with
| some idx => get >>= λ ctx =>
  match ctx.uVals.get! idx with
  | none => pure l
  | some v => pure v
| none => pure l

def uAssignIdx (idx : Nat) (l : Level) : State Context Unit :=
modify $ λ ctx => { uVals := ctx.uVals.set idx (some l) .. ctx }

def uAssign (umvar : Level) (l : Level) : State Context Unit :=
match uMetaIdx umvar with
| some idx => modify $ λ ctx => { uVals := ctx.uVals.set idx (some l) .. ctx }
| _        => panic! "uassign called on non-(tmp-)mvar"

partial def uFind (f : Level → Bool) : Level → Bool
| l =>
  if f l
  then true
  else
    match l with
    | Level.succ l     => uFind l
    | Level.max l₁ l₂  => uFind l₁ || uFind l₂
    | Level.imax l₁ l₂ => uFind l₁ || uFind l₂
    | _                => false

def uOccursIn (l₀ : Level) (l : Level) : Bool :=
uFind (λ l => l == l₀) l

def uHasTmpMVar (l : Level) : Bool :=
uFind uIsMeta l

partial def uUnify : Level → Level → EState String Context Unit
| l₁, l₂ => do
  l₁ ← EState.fromState $ uShallowInstantiate l₁;
  l₂ ← EState.fromState $ uShallowInstantiate l₂;
  if uIsMeta l₂ && !(uIsMeta l₁)
  then uUnify l₂ l₁
  else
    match l₁, l₂ with
    | Level.zero,         Level.zero         => pure ()
    | Level.param p₁,     Level.param p₂     => when (p₁ ≠ p₂) $ throw "Level.param clash"
    | Level.succ  l₁,     Level.succ  l₂     => uUnify l₁ l₂
    | Level.max l₁₁ l₁₂,  Level.max l₂₁ l₂₂  => uUnify l₁₁ l₂₁ *> uUnify l₁₂ l₂₂
    | Level.imax l₁₁ l₁₂, Level.imax l₂₁ l₂₂ => uUnify l₁₁ l₂₁ *> uUnify l₁₂ l₂₂
    | Level.mvar _,       _                  =>
      match uMetaIdx l₁ with
      | none     => when (!(l₁ == l₂)) $ throw "Level.mvar clash"
      | some idx => do when (uOccursIn l₁ l₂) $ throw  "occurs";
                       EState.fromState $ uAssignIdx idx l₂
    | _, _ => throw $ "lUnify: " ++ toString l₁ ++ " !=?= " ++ toString l₂

partial def uInstantiate (ctx : Context) : Level → Level
| l => if (!l.hasMVar)
       then l
       else
         match uMetaIdx l with
         | some idx => match (Context.uLookupIdx idx).run' ctx with
                       | some t => uInstantiate t
                       | none   => l
         | none =>
           match l with
           | Level.succ l     => Level.succ $ uInstantiate l
           | Level.max l₁ l₂  => Level.max (uInstantiate l₁) (uInstantiate l₂)
           | Level.imax l₁ l₂ => Level.imax (uInstantiate l₁) (uInstantiate l₂)
           | _ => l

-- Expressions and Levels

def eHasTmpMVar (e : Expr) : Bool :=
if e.hasMVar
then eFind (λ t => eIsMeta t || (t.isConst && t.constLevels.any uHasTmpMVar)) e
else false

partial def slowWhnfApp : Expr → List Expr → Expr
| (Expr.lam _ _ d b), (arg::args) => slowWhnfApp (b.instantiate1 arg) args
| f, args => mkApp f args

partial def slowWhnf : Expr → Expr
| e => if e.isApp then slowWhnfApp (slowWhnf e.getAppFn) e.getAppArgs else e

partial def eUnify : Expr → Expr → EState String Context Unit
| e₁, e₂ =>
  if !e₁.hasMVar && !e₂.hasMVar
  then unless (e₁ == e₂) $ throw $ "eUnify: " ++ toString e₁ ++ " !=?= " ++ toString e₂
  else do
    e₁ ← slowWhnf <$> (EState.fromState $ eShallowInstantiate e₁);
    e₂ ← slowWhnf <$> (EState.fromState $ eShallowInstantiate e₂);
    if e₁.isMVar && e₂.isMVar && e₁ == e₂ then pure ()
    else if eIsMeta e₂ && !(eIsMeta e₁) then eUnify e₂ e₁
    else if e₁.isBVar && e₂.isBVar && e₁.bvarIdx == e₂.bvarIdx then pure ()
    else if e₁.isFVar && e₂.isFVar && e₁.fvarName == e₂.fvarName then pure ()
    else if e₁.isConst && e₂.isConst && e₁.constName == e₂.constName then
      List.mfor₂ uUnify e₁.constLevels e₂.constLevels
    else if e₁.isApp && e₂.isApp && e₁.getAppArgs.length == e₂.getAppArgs.length then
      eUnify e₁.getAppFn e₂.getAppFn *> List.mfor₂ eUnify e₁.getAppArgs e₂.getAppArgs
    else if e₁.isForall && e₂.isForall then do
      eUnify e₁.bindingDomain e₂.bindingDomain;
      eUnify e₁.bindingBody e₂.bindingBody
    else if eIsMeta e₁ && !(eOccursIn e₂ e₁) then
      match eMetaIdx e₁ with
      | some idx => EState.fromState $ eAssignIdx idx e₂
      | none     => panic! "UNREACHABLE"
    else
      throw $ "eUnify: " ++ toString e₁ ++ " !=?= " ++ toString e₂

partial def eInstantiate (ctx : Context) : Expr → Expr
| e =>
  if !e.hasMVar -- conservative check (includes regular mvars as well)
  then e
  else
    match e with
    | Expr.pi n i d b  => Expr.pi n i (eInstantiate d) (eInstantiate b)
    | Expr.lam n i d b => Expr.lam n i (eInstantiate d) (eInstantiate b)
    | Expr.const n ls  => Expr.const n (ls.map $ uInstantiate ctx)
    | Expr.app e₁ e₂   => Expr.app (eInstantiate e₁) (eInstantiate e₂)
    | _ =>
      match eMetaIdx e with
      | none     => e
      | some idx => do
        match (eLookupIdx idx).run' ctx with
        | some t => eInstantiate t
        | none   => e

-- AlphaNormalization

structure AlphaNormData : Type :=
(eRenameMap : RBMap Nat Nat (λ n₁ n₂ => n₁ < n₂) := mkRBMap _ _ _)
(uRenameMap : RBMap Nat Nat (λ n₁ n₂ => n₁ < n₂) := mkRBMap _ _ _)

partial def uAlphaNormalizeCore : Level → State AlphaNormData Level
| l =>
  match l with
  | Level.zero        => pure l
  | Level.param _     => pure l
  | Level.succ l      => do l ← uAlphaNormalizeCore l;
                           pure $ Level.succ l
  | Level.max l₁ l₂   => do l₁ ← uAlphaNormalizeCore l₁;
                           l₂ ← uAlphaNormalizeCore l₂;
                           pure $ Level.max l₁ l₂
  | Level.imax l₁ l₂  => do l₁ ← uAlphaNormalizeCore l₁;
                            l₂ ← uAlphaNormalizeCore l₂;
                            pure $ Level.imax l₁ l₂
  | Level.mvar m      =>
    match uMetaIdx l with
    | none     => pure l
    | some idx => do
      lookupStatus ← get >>= λ ϕ => pure $ ϕ.uRenameMap.find idx;
      match lookupStatus with
      | none => do
        l ← get >>= λ ϕ => pure $ Level.mvar (mkNumName alphaMetaPrefix ϕ.uRenameMap.size);
        modify $ λ ϕ => { uRenameMap := ϕ.uRenameMap.insert idx ϕ.uRenameMap.size .. ϕ };
        pure l
      | some alphaIdx => pure $ Level.mvar (mkNumName alphaMetaPrefix alphaIdx)

partial def eAlphaNormalizeCore : Expr → State AlphaNormData Expr
| e =>
  if e.isConst then pure e
  else if e.isFVar then pure e
  else if !e.hasMVar then pure e
  else match e with
       | Expr.app f a => do
         f ← eAlphaNormalizeCore f;
         a ← eAlphaNormalizeCore a;
         pure $ Expr.app f a
       | Expr.pi n i d b => do
         d ← eAlphaNormalizeCore d;
         b ← eAlphaNormalizeCore b;
         pure $ Expr.pi n i d b
       | _ =>
         match eMetaIdx e with
         | none     => pure e
         | some idx => do
           lookupStatus ← get >>= λ ϕ => pure $ ϕ.eRenameMap.find idx;
           match lookupStatus with
           | none => do
             e ← get >>= λ ϕ => pure $ Expr.mvar (mkNumName alphaMetaPrefix ϕ.eRenameMap.size);
             modify $ λ ϕ => { eRenameMap := ϕ.eRenameMap.insert idx ϕ.eRenameMap.size .. ϕ };
             pure e
           | some alphaIdx => pure $ Expr.mvar (mkNumName alphaMetaPrefix alphaIdx)

def αNorm (e : Expr) : Expr :=
(eAlphaNormalizeCore e).run' {}

end Context
end TypeClass
end Lean
