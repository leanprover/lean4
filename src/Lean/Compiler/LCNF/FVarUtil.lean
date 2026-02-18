/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM

public section

namespace Lean.Compiler.LCNF

class TraverseFVar (α : Type) where
  mapFVarM {m : Type → Type} [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (val : α) : m α
  forFVarM {m : Type → Type} [Monad m] (f : FVarId → m Unit) (val : α) : m Unit

export TraverseFVar (mapFVarM forFVarM)

partial def Expr.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (e : Expr) : m Expr := do
  if e.hasFVar then
    match e with
    | .app fn arg => return e.updateApp! (← mapFVarM f fn) (← mapFVarM f arg)
    | .fvar fvarId => return e.updateFVar! (← f fvarId)
    | .lam _ ty body _ => return e.updateLambdaE! (← mapFVarM f ty) (← mapFVarM f body)
    | .forallE _ ty body _ => return e.updateForallE! (← mapFVarM f ty) (← mapFVarM f body)
    | .bvar .. | .sort .. => return e
    | .mdata .. | .const .. | .lit .. => return e
    | .letE ..  | .proj .. | .mvar .. => unreachable! -- LCNF types do not have this kind of expr
  else
    return e

partial def Expr.forFVarM [Monad m] (f : FVarId → m Unit) (e : Expr) : m Unit := do
  if e.hasFVar then
    match e with
    | .app fn arg =>
      forFVarM f fn
      forFVarM f arg
    | .fvar fvarId => f fvarId
    | .lam _ ty body .. =>
      forFVarM f ty
      forFVarM f body
    | .forallE _ ty body .. =>
      forFVarM f ty
      forFVarM f body
    | .bvar .. | .sort .. => return
    | .mdata .. | .const .. | .lit .. => return
    | .mvar .. | .letE .. | .proj .. => unreachable! -- LCNF types do not have this kind of expr
  else
    return ()

instance : TraverseFVar Expr where
  mapFVarM := Expr.mapFVarM
  forFVarM := Expr.forFVarM

def Arg.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (arg : Arg pu) : m (Arg pu) := do
  match arg with
  | .erased => return .erased
  | .type e _ => return arg.updateType! (← TraverseFVar.mapFVarM f e)
  | .fvar fvarId => return arg.updateFVar! (← f fvarId)

def Arg.forFVarM [Monad m] (f : FVarId → m Unit) (arg : Arg pu) : m Unit := do
  match arg with
  | .erased => return ()
  | .type e _ => TraverseFVar.forFVarM f e
  | .fvar fvarId => f fvarId

instance : TraverseFVar (Arg pu) where
  mapFVarM := Arg.mapFVarM
  forFVarM := Arg.forFVarM

def LetValue.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (e : LetValue pu) : m (LetValue pu) := do
  match e with
  | .lit .. | .erased => return e
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _ =>
    return e.updateProj! (← f fvarId)
  | .const _ _ args _ | .pap _ args _ | .fap _ args _ | .ctor _ args _ =>
    return e.updateArgs! (← args.mapM (TraverseFVar.mapFVarM f))
  | .fvar fvarId args => return e.updateFVar! (← f fvarId) (← args.mapM (TraverseFVar.mapFVarM f))
  | .reset n fvarId _ => return e.updateReset! n (← f fvarId)
  | .reuse fvarId i updateHeader args _ =>
    return e.updateReuse! (← f fvarId) i updateHeader (← args.mapM (TraverseFVar.mapFVarM f))
  | .box ty fvarId _ => return e.updateBox! ty (← f fvarId)
  | .unbox fvarId _ => return e.updateUnbox! (← f fvarId)

def LetValue.forFVarM [Monad m] (f : FVarId → m Unit) (e : LetValue pu) : m Unit := do
  match e with
  | .lit .. | .erased => return ()
  | .proj _ _ fvarId _ | .oproj _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _
  | .reset _ fvarId _ | .box _ fvarId _ | .unbox fvarId _ => f fvarId
  | .const _ _ args _ | .pap _ args _ | .fap _ args _ | .ctor _ args _ =>
    args.forM (TraverseFVar.forFVarM f)
  | .fvar fvarId args | .reuse fvarId _ _ args _ => f fvarId; args.forM (TraverseFVar.forFVarM f)

instance : TraverseFVar (LetValue pu) where
  mapFVarM := LetValue.mapFVarM
  forFVarM := LetValue.forFVarM

partial def LetDecl.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (decl : LetDecl pu) : m (LetDecl pu) := do
  decl.update (← Expr.mapFVarM f decl.type) (← LetValue.mapFVarM f decl.value)

partial def LetDecl.forFVarM [Monad m] (f : FVarId → m Unit) (decl : LetDecl pu) : m Unit := do
  Expr.forFVarM f decl.type
  LetValue.forFVarM f decl.value

instance : TraverseFVar (LetDecl pu) where
  mapFVarM := LetDecl.mapFVarM
  forFVarM := LetDecl.forFVarM

partial def Param.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (param : Param pu) : m (Param pu) := do
  param.update (← Expr.mapFVarM f param.type)

partial def Param.forFVarM [Monad m] (f : FVarId → m Unit) (param : Param pu) : m Unit := do
  Expr.forFVarM f param.type

instance : TraverseFVar (Param pu) where
  mapFVarM := Param.mapFVarM
  forFVarM := Param.forFVarM

partial def Code.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (c : Code pu) : m (Code pu) := do
  match c with
  | .let decl k =>
    let decl ← LetDecl.mapFVarM f decl
    return Code.updateLet! c decl (← mapFVarM f k)
  | .fun decl k _ =>
    let params ← decl.params.mapM (Param.mapFVarM f)
    let decl ← decl.update (← Expr.mapFVarM f decl.type) params (← mapFVarM f decl.value)
    return Code.updateFun! c decl (← mapFVarM f k)
  | .jp decl k =>
    let params ← decl.params.mapM (Param.mapFVarM f)
    let decl ← decl.update (← Expr.mapFVarM f decl.type) params (← mapFVarM f decl.value)
    return Code.updateFun! c decl (← mapFVarM f k)
  | .cases cs =>
    return Code.updateCases! c (← Expr.mapFVarM f cs.resultType) (← f cs.discr) (← cs.alts.mapM (·.mapCodeM (mapFVarM f)))
  | .jmp fn args =>
    return Code.updateJmp! c (← f fn) (← args.mapM (Arg.mapFVarM f))
  | .return var =>
    return Code.updateReturn! c (← f var)
  | .unreach typ =>
    return Code.updateUnreach! c (← Expr.mapFVarM f typ)
  | .sset fvarId i offset y ty k _ =>
    return Code.updateSset! c (← f fvarId) i offset (← f y) (← Expr.mapFVarM f ty) (← mapFVarM f k)
  | .uset fvarId offset y k _ =>
    return Code.updateUset! c (← f fvarId) offset (← f y) (← mapFVarM f k)
  | .inc fvarId n check persistent k _ =>
    return Code.updateInc! c (← f fvarId) n check persistent (← mapFVarM f k)
  | .dec fvarId n check persistent k _ =>
    return Code.updateDec! c (← f fvarId) n check persistent (← mapFVarM f k)

partial def Code.forFVarM [Monad m] (f : FVarId → m Unit) (c : Code pu) : m Unit := do
  match c with
  | .let decl k =>
    LetDecl.forFVarM f decl
    forFVarM f k
  | .fun decl k _ =>
    decl.params.forM (Param.forFVarM f)
    Expr.forFVarM f decl.type
    forFVarM f decl.value
    forFVarM f k
  | .jp decl k =>
    decl.params.forM (Param.forFVarM f)
    Expr.forFVarM f decl.type
    forFVarM f decl.value
    forFVarM f k
  | .cases cs =>
    Expr.forFVarM f cs.resultType
    f cs.discr
    cs.alts.forM (·.forCodeM (forFVarM f))
  | .jmp fn args =>
    f fn
    args.forM (Arg.forFVarM f)
  | .return var => f var
  | .unreach typ =>
    Expr.forFVarM f typ
  | .sset fvarId _ _ y ty k _ =>
    f fvarId
    f y
    Expr.forFVarM f ty
    forFVarM f k
  | .uset fvarId _ y k _ =>
    f fvarId
    f y
    forFVarM f k
  | .inc (fvarId := fvarId) (k := k) .. | .dec (fvarId := fvarId) (k := k) .. =>
    f fvarId
    forFVarM f k

instance : TraverseFVar (Code pu) where
  mapFVarM := Code.mapFVarM
  forFVarM := Code.forFVarM

def FunDecl.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (decl : FunDecl pu) : m (FunDecl pu) := do
  let params ← decl.params.mapM (Param.mapFVarM f)
  decl.update (← Expr.mapFVarM f decl.type) params (← Code.mapFVarM f decl.value)

def FunDecl.forFVarM [Monad m] (f : FVarId → m Unit) (decl : FunDecl pu) : m Unit := do
  decl.params.forM (Param.forFVarM f)
  Expr.forFVarM f decl.type
  Code.forFVarM f decl.value

instance : TraverseFVar (FunDecl pu) where
  mapFVarM := FunDecl.mapFVarM
  forFVarM := FunDecl.forFVarM

instance : TraverseFVar (CodeDecl pu) where
  mapFVarM f decl := do
    match decl with
    | .fun decl _ => return .fun (← mapFVarM f decl)
    | .jp decl => return .jp (← mapFVarM f decl)
    | .let decl => return .let (← mapFVarM f decl)
    | .uset var i y _ => return .uset (← f var) i (← f y)
    | .sset var i offset y ty _ => return .sset (← f var) i offset (← f y) (← mapFVarM f ty)
    | .inc fvarId n check persistent _ => return .inc (← f fvarId) n check persistent
    | .dec fvarId n check persistent _ => return .dec (← f fvarId) n check persistent
  forFVarM f decl :=
    match decl with
    | .fun decl _ => forFVarM f decl
    | .jp decl => forFVarM f decl
    | .let decl => forFVarM f decl
    | .uset var i y _ => do f var; f y
    | .sset var i offset y ty _ => do f var; f y; forFVarM f ty
    | .inc (fvarId := fvarId) .. | .dec (fvarId := fvarId) .. => f fvarId

instance : TraverseFVar (Alt pu) where
  mapFVarM f alt := do
    match alt with
    | .alt ctor params c _ =>
      let params ← params.mapM (Param.mapFVarM f)
      return .alt ctor params (← Code.mapFVarM f c)
    | .default c => return .default (← Code.mapFVarM f c)
    | .ctorAlt i c _ => return .ctorAlt i (← Code.mapFVarM f c)
  forFVarM f alt := do
    match alt with
    | .alt _ params c _ =>
      params.forM (Param.forFVarM f)
      Code.forFVarM f c
    | .default c => Code.forFVarM f c
    | .ctorAlt i c _ => Code.forFVarM f c

def anyFVarM [Monad m] [TraverseFVar α] (f : FVarId → m Bool) (x : α) : m Bool := do
  return (← TraverseFVar.forFVarM go x |>.run) matches none
where
  go (fvar : FVarId) : OptionT m Unit := do
    if (← f fvar) then failure

def allFVarM [Monad m] [TraverseFVar α] (f : FVarId → m Bool) (x : α) : m Bool := do
  return (← TraverseFVar.forFVarM go x |>.run) matches .some ..
where
  go (fvar : FVarId) : OptionT m Unit := do
    if !(← f fvar) then failure

def anyFVar [TraverseFVar α] (f : FVarId → Bool) (x : α) : Bool :=
  Id.run <| anyFVarM (pure <| f ·) x

def allFVar [TraverseFVar α] (f : FVarId → Bool) (x : α) : Bool :=
  Id.run <| allFVarM (pure <| f ·) x

end Lean.Compiler.LCNF
