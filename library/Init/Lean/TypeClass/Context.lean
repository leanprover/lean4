/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Custom unifier for tabled typeclass resolution.

Note: this file will be removed once the unifier is implemented in Lean.
-/
prelude
import Init.Data.Nat
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

abbrev ContextFn : Type → Type := EStateM ContextFail Context

namespace Context

def metaPrefix : Name :=
mkSimpleName "_tc_meta"

def alphaMetaPrefix : Name :=
mkSimpleName "_tc_alpha"

-- Expressions

def eMetaIdx : Expr → Option Nat
| Expr.mvar (Name.mkNumeral n idx) _ => guard (n == metaPrefix) *> pure idx
| _ => none

def eIsMeta (e : Expr) : Bool := (eMetaIdx e).toBool

def eNewMeta (type : Expr) : StateM Context Expr :=
do ctx ← get;
   let idx := ctx.eTypes.size;
   set { eTypes := ctx.eTypes.push type, eVals := ctx.eVals.push none, .. ctx };
   pure $ mkMVar (mkNumName metaPrefix idx)

def eLookupIdx (idx : Nat) : StateM Context (Option Expr) :=
do ctx ← get; pure $ ctx.eVals.get! idx

partial def eShallowInstantiate : Expr → StateM Context Expr
| e =>
  match eMetaIdx e with
  | some idx => get >>= λ ctx =>
    match ctx.eVals.get! idx with
    | none => pure e
    | some v => eShallowInstantiate v
  | none => pure e

def eInferIdx (idx : Nat) : StateM Context Expr :=
do ctx ← get; pure $ ctx.eTypes.get! idx

def eInfer (ctx : Context) (mvar : Expr) : Expr :=
match eMetaIdx mvar with
| some idx => ctx.eTypes.get! idx
| none     => panic! "eInfer called on non-(tmp-)mvar"

def eAssignIdx (idx : Nat) (e : Expr) : StateM Context Unit :=
modify $ λ ctx => { eVals := ctx.eVals.set idx (some e) .. ctx }

def eAssign (mvar : Expr) (e : Expr) : StateM Context Unit :=
match eMetaIdx mvar with
| some idx => modify $ λ ctx => { eVals := ctx.eVals.set idx (some e) .. ctx }
| _        => panic! "eAssign called on non-(tmp-)mvar"

partial def eFind (f : Expr → Bool) : Expr → Bool
| e =>
  if f e
  then true
  else
    match e with
    | Expr.app f a _ => eFind f || eFind a
    | Expr.forallE _ d b _ => eFind d || eFind b
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

def uNewMeta : StateM Context Level :=
do ctx ← get;
   let idx := ctx.uVals.size;
   set { uVals := ctx.uVals.push none, .. ctx };
   pure $ mkLevelMVar (mkNumName metaPrefix idx)

def uLookupIdx (idx : Nat) : StateM Context (Option Level) :=
do ctx ← get; pure $ ctx.uVals.get! idx

partial def uShallowInstantiate : Level → StateM Context Level
| l =>
  match uMetaIdx l with
  | some idx => get >>= λ ctx =>
    match ctx.uVals.get! idx with
    | none => pure l
    | some v => uShallowInstantiate v
  | none => pure l

def uAssignIdx (idx : Nat) (l : Level) : StateM Context Unit :=
modify $ λ ctx => { uVals := ctx.uVals.set idx (some l) .. ctx }

def uAssign (umvar : Level) (l : Level) : StateM Context Unit :=
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

partial def uUnify : Level → Level → EStateM String Context Unit
| l₁, l₂ => do
  l₁ ← EStateM.fromStateM $ uShallowInstantiate l₁;
  l₂ ← EStateM.fromStateM $ uShallowInstantiate l₂;
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
                       EStateM.fromStateM $ uAssignIdx idx l₂
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
           | Level.succ l     => mkLevelSucc $ uInstantiate l
           | Level.max l₁ l₂  => mkLevelMax (uInstantiate l₁) (uInstantiate l₂)
           | Level.imax l₁ l₂ => mkLevelIMax (uInstantiate l₁) (uInstantiate l₂)
           | _ => l

-- Expressions and Levels

def eHasTmpMVar (e : Expr) : Bool :=
if e.hasMVar
then eFind (λ t => eIsMeta t || (t.isConst && t.constLevels!.any uHasTmpMVar)) e
else false

partial def slowWhnfApp (args : Array Expr) : Expr → Nat → Expr
| f@(Expr.lam _ d b _), i =>
  if h : i < args.size then
    slowWhnfApp (b.instantiate1 (args.get ⟨i, h⟩)) (i+1)
  else
    f
| f, i =>
  if h : i < args.size then
    slowWhnfApp (mkApp f (args.get ⟨i, h⟩)) (i+1)
  else
    f

partial def slowWhnf : Expr → Expr
| e => if e.isApp then slowWhnfApp e.getAppArgs (slowWhnf e.getAppFn) 0 else e

partial def eUnify : Expr → Expr → EStateM String Context Unit
| e₁, e₂ =>
  if !e₁.hasMVar && !e₂.hasMVar
  then unless (e₁ == e₂) $ throw $ "eUnify: " ++ toString e₁ ++ " !=?= " ++ toString e₂
  else do
    e₁ ← slowWhnf <$> (EStateM.fromStateM $ eShallowInstantiate e₁);
    e₂ ← slowWhnf <$> (EStateM.fromStateM $ eShallowInstantiate e₂);
    if e₁.isMVar && e₂.isMVar && e₁ == e₂ then pure ()
    else if eIsMeta e₂ && !(eIsMeta e₁) then eUnify e₂ e₁
    else if e₁.isBVar && e₂.isBVar && e₁.bvarIdx! == e₂.bvarIdx! then pure ()
    else if e₁.isFVar && e₂.isFVar && e₁.fvarId! == e₂.fvarId! then pure ()
    else if e₁.isConst && e₂.isConst && e₁.constName! == e₂.constName! then
      List.forM₂ uUnify e₁.constLevels! e₂.constLevels!
    else if e₁.isApp && e₂.isApp && e₁.getAppNumArgs == e₂.getAppNumArgs then do
      let args₁ := e₁.getAppArgs;
      let args₂ := e₂.getAppArgs;
      eUnify e₁.getAppFn e₂.getAppFn;
      args₁.size.forM $ fun i => eUnify (args₁.get! i) (args₂.get! i)
    else if e₁.isForall && e₂.isForall then do
      eUnify e₁.bindingDomain! e₂.bindingDomain!;
      eUnify e₁.bindingBody! e₂.bindingBody!
    else if eIsMeta e₁ && !(eOccursIn e₂ e₁) then
      match eMetaIdx e₁ with
      | some idx => EStateM.fromStateM $ eAssignIdx idx e₂
      | none     => panic! "UNREACHABLE"
    else
      throw $ "eUnify: " ++ toString e₁ ++ " !=?= " ++ toString e₂

partial def eInstantiate (ctx : Context) : Expr → Expr
| e =>
  if !e.hasMVar -- conservative check (includes regular mvars as well)
  then e
  else
    match e with
    | Expr.forallE n d b c => mkForall n c.binderInfo (eInstantiate d) (eInstantiate b)
    | Expr.lam n d b c     => mkLambda n c.binderInfo (eInstantiate d) (eInstantiate b)
    | Expr.const n ls _    => mkConst n (ls.map $ uInstantiate ctx)
    | Expr.app e₁ e₂ _     => mkApp (eInstantiate e₁) (eInstantiate e₂)
    | _ =>
      match eMetaIdx e with
      | none     => e
      | some idx => do
        match (eLookupIdx idx).run' ctx with
        | some t => eInstantiate t
        | none   => e

-- AlphaNormalization

structure MetaNormData (α : Type) : Type :=
(ctx        : α)
(eRenameMap : RBMap Nat Nat (λ n₁ n₂ => n₁ < n₂) := mkRBMap _ _ _)
(uRenameMap : RBMap Nat Nat (λ n₁ n₂ => n₁ < n₂) := mkRBMap _ _ _)

structure MetaNormFuncs (α : Type) : Type :=
(uNewMeta   : Nat → StateM (MetaNormData α) Level)
(uMkMeta    : Nat → StateM (MetaNormData α) Level)
(eNewMeta   : Nat → StateM (MetaNormData α) Expr)
(eMkMeta    : Nat → StateM (MetaNormData α) Expr)

partial def uMetaNormalizeCore {α : Type} (fs : MetaNormFuncs α) : Level → StateM (MetaNormData α) Level
| l =>
  if !l.hasMVar then pure l else
    match l with
    | Level.zero        => pure l
    | Level.param _     => pure l
    | Level.succ l      => do l ← uMetaNormalizeCore l;
                             pure $ mkLevelSucc l
    | Level.max l₁ l₂   => do l₁ ← uMetaNormalizeCore l₁;
                             l₂ ← uMetaNormalizeCore l₂;
                             pure $ mkLevelMax l₁ l₂
    | Level.imax l₁ l₂  => do l₁ ← uMetaNormalizeCore l₁;
                              l₂ ← uMetaNormalizeCore l₂;
                              pure $ mkLevelIMax l₁ l₂
    | Level.mvar m      =>
      match uMetaIdx l with
      | none     => pure l
      | some idx =>  do
        lookupStatus ← get >>= λ ϕ => pure $ ϕ.uRenameMap.find idx;
        match lookupStatus with
        | none => fs.uNewMeta idx
        | some idx => fs.uMkMeta idx

partial def eMetaNormalizeCore {α : Type} (fs : MetaNormFuncs α) : Expr → StateM (MetaNormData α) Expr
| e =>
  if e.isConst then do
    ls ← e.constLevels!.mapM (uMetaNormalizeCore fs);
    pure $ Expr.updateConst! e ls
  else if e.isFVar then pure e
  else if !e.hasMVar then pure e
  else match e with
       | Expr.app f a _ => do
         f ← eMetaNormalizeCore f;
         a ← eMetaNormalizeCore a;
         pure $ mkApp f a
       | Expr.forallE n d b c => do
         d ← eMetaNormalizeCore d;
         b ← eMetaNormalizeCore b;
         pure $ mkForall n c.binderInfo d b
       | _ =>
         match eMetaIdx e with
         | none     => pure e
         | some idx => do
           lookupStatus ← get >>= λ ϕ => pure $ ϕ.eRenameMap.find idx;
           match lookupStatus with
           | none => fs.eNewMeta idx
           | some idx => fs.eMkMeta idx

def αNorm (e : Expr) : Expr :=
let fs : MetaNormFuncs Unit := {
  uNewMeta := λ idx => do {
    l ← get >>= λ ϕ => pure $ mkLevelMVar (mkNumName alphaMetaPrefix ϕ.uRenameMap.size);
    modify $ λ ϕ => { uRenameMap := ϕ.uRenameMap.insert idx ϕ.uRenameMap.size .. ϕ };
    pure l },
  uMkMeta := λ idx => pure $ mkLevelMVar (mkNumName alphaMetaPrefix idx),
  eNewMeta := λ idx => do {
    e ← get >>= λ ϕ => pure $ mkMVar (mkNumName alphaMetaPrefix ϕ.eRenameMap.size);
    modify $ λ ϕ => { eRenameMap := ϕ.eRenameMap.insert idx ϕ.eRenameMap.size .. ϕ };
    pure e },
  eMkMeta := λ idx => pure $ mkMVar (mkNumName alphaMetaPrefix idx)
};
(eMetaNormalizeCore fs e).run' { ctx := () }

def internalize (oldCtx : Context) (val type : Expr) (newCtx : Context) : Expr × Expr × Context :=
let fs : MetaNormFuncs (Context × Context) := {
  uNewMeta := λ idx => do {
    (oldCtx, newCtx) ← get >>= λ ϕ => pure ϕ.ctx;
    (l, newCtx) ← pure $ StateT.run Context.uNewMeta newCtx;
    match Context.uMetaIdx l with
    | some newIdx => modify $ λ ϕ => { ctx := (oldCtx, newCtx), uRenameMap := ϕ.uRenameMap.insert idx newIdx, .. ϕ }
    | none => panic "unreachable";
    pure l },
  uMkMeta := λ idx => pure $ mkLevelMVar (mkNumName metaPrefix idx),
  eNewMeta := λ idx => do {
    (oldCtx, newCtx) ← get >>= λ ϕ => pure ϕ.ctx;
    (e, newCtx) ← pure $ StateT.run (Context.eNewMeta $ oldCtx.eTypes.get! idx) newCtx;
    match Context.eMetaIdx e with
    | some newIdx => modify $ λ ϕ => { ctx := (oldCtx, newCtx), eRenameMap := ϕ.eRenameMap.insert idx newIdx, .. ϕ }
    | none => panic "unreachable";
    pure e },
  eMkMeta := λ idx => pure $ mkMVar (mkNumName metaPrefix idx)
};
match (do newType ← eMetaNormalizeCore fs type; newVal ← eMetaNormalizeCore fs val; pure (newVal, newType)).run { ctx := (oldCtx, newCtx) } with
| ((newVal, newType), ϕ) => (newVal, newType, ϕ.ctx.2)

end Context
end TypeClass
end Lean
