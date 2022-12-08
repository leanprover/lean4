/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Expr
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

class TraverseFVar (α : Type) where
  mapFVarM {m : Type → Type} [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (val : α) : m α
  forFVarM {m : Type → Type} [Monad m] (f : FVarId → m Unit) (val : α) : m Unit

export TraverseFVar (mapFVarM forFVarM)

partial def Expr.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (e : Expr) : m Expr := do
  match e with
  | .app fn arg => return e.updateApp! (← mapFVarM f fn) (← mapFVarM f arg)
  | .fvar fvarId => return e.updateFVar! (← f fvarId)
  | .lam _ ty body _ => return e.updateLambdaE! (← mapFVarM f ty) (← mapFVarM f body)
  | .forallE _ ty body _ => return e.updateForallE! (← mapFVarM f ty) (← mapFVarM f body)
  | .bvar .. | .sort .. => return e
  | .mdata .. | .const .. | .lit .. => return e
  | .letE ..  | .proj .. | .mvar .. => unreachable! -- LCNF types do not have this kind of expr

partial def Expr.forFVarM [Monad m] (f : FVarId → m Unit) (e : Expr) : m Unit := do
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

instance : TraverseFVar Expr where
  mapFVarM := Expr.mapFVarM
  forFVarM := Expr.forFVarM

def Arg.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (arg : Arg) : m Arg := do
  match arg with
  | .erased => return .erased
  | .type e => return arg.updateType! (← TraverseFVar.mapFVarM f e)
  | .fvar fvarId => return arg.updateFVar! (← f fvarId)

def Arg.forFVarM [Monad m] (f : FVarId → m Unit) (arg : Arg) : m Unit := do
  match arg with
  | .erased => return ()
  | .type e => TraverseFVar.forFVarM f e
  | .fvar fvarId => f fvarId

instance : TraverseFVar Arg where
  mapFVarM := Arg.mapFVarM
  forFVarM := Arg.forFVarM

def LetValue.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (e : LetValue) : m LetValue := do
  match e with
  | .value .. | .erased => return e
  | .proj _ _ fvarId => return e.updateProj! (← f fvarId)
  | .const _ _ args => return e.updateArgs! (← args.mapM (TraverseFVar.mapFVarM f))
  | .fvar fvarId args => return e.updateFVar! (← f fvarId) (← args.mapM (TraverseFVar.mapFVarM f))

def LetValue.forFVarM [Monad m] (f : FVarId → m Unit) (e : LetValue) : m Unit := do
  match e with
  | .value .. | .erased => return ()
  | .proj _ _ fvarId => f fvarId
  | .const _ _ args => args.forM (TraverseFVar.forFVarM f)
  | .fvar fvarId args => f fvarId; args.forM (TraverseFVar.forFVarM f)

instance : TraverseFVar LetValue where
  mapFVarM := LetValue.mapFVarM
  forFVarM := LetValue.forFVarM

partial def LetDecl.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (decl : LetDecl) : m LetDecl := do
  decl.update (← Expr.mapFVarM f decl.type) (← LetValue.mapFVarM f decl.value)

partial def LetDecl.forFVarM [Monad m] (f : FVarId → m Unit) (decl : LetDecl) : m Unit := do
  Expr.forFVarM f decl.type
  LetValue.forFVarM f decl.value

instance : TraverseFVar LetDecl where
  mapFVarM := LetDecl.mapFVarM
  forFVarM := LetDecl.forFVarM

partial def Param.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (param : Param) : m Param := do
  param.update (← Expr.mapFVarM f param.type)

partial def Param.forFVarM [Monad m] (f : FVarId → m Unit) (param : Param) : m Unit := do
  Expr.forFVarM f param.type

instance : TraverseFVar Param where
  mapFVarM := Param.mapFVarM
  forFVarM := Param.forFVarM

partial def Code.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (c : Code) : m Code := do
  match c with
  | .let decl k =>
    let decl ← LetDecl.mapFVarM f decl
    return Code.updateLet! c decl (← mapFVarM f k)
  | .fun decl k =>
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

partial def Code.forFVarM [Monad m] (f : FVarId → m Unit) (c : Code) : m Unit := do
  match c with
  | .let decl k =>
    LetDecl.forFVarM f decl
    forFVarM f k
  | .fun decl k =>
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

instance : TraverseFVar Code where
  mapFVarM := Code.mapFVarM
  forFVarM := Code.forFVarM

def FunDecl.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (decl : FunDecl) : m FunDecl := do
  let params ← decl.params.mapM (Param.mapFVarM f)
  decl.update (← Expr.mapFVarM f decl.type) params (← Code.mapFVarM f decl.value)

def FunDecl.forFVarM [Monad m] (f : FVarId → m Unit) (decl : FunDecl) : m Unit := do
  decl.params.forM (Param.forFVarM f)
  Expr.forFVarM f decl.type
  Code.forFVarM f decl.value

instance : TraverseFVar FunDecl where
  mapFVarM := FunDecl.mapFVarM
  forFVarM := FunDecl.forFVarM

instance : TraverseFVar CodeDecl where
  mapFVarM f decl := do
    match decl with
    | .fun decl => return .fun (← mapFVarM f decl)
    | .jp decl => return .jp (← mapFVarM f decl)
    | .let decl => return .let (← mapFVarM f decl)
  forFVarM f decl :=
    match decl with
    | .fun decl => forFVarM f decl
    | .jp decl => forFVarM f decl
    | .let decl => forFVarM f decl

instance : TraverseFVar Alt where
  mapFVarM f alt := do
    match alt with
    | .alt ctor params c =>
      let params ← params.mapM (Param.mapFVarM f)
      return .alt ctor params (← Code.mapFVarM f c)
    | .default c => return .default (← Code.mapFVarM f c)
  forFVarM f alt := do
    match alt with
    | .alt _ params c =>
      params.forM (Param.forFVarM f)
      Code.forFVarM f c
    | .default c => Code.forFVarM f c

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
  Id.run <| anyFVarM f x

def allFVar [TraverseFVar α] (f : FVarId → Bool) (x : α) : Bool :=
  Id.run <| allFVarM f x

end Lean.Compiler.LCNF
