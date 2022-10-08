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
  | .proj typ idx struct => return .proj typ idx (← mapFVarM f struct)
  | .app fn arg => return .app (← mapFVarM f fn) (← mapFVarM f arg)
  | .fvar fvarId => return .fvar (← f fvarId)
  | .lam arg ty body bi =>
    return .lam arg (← mapFVarM f ty) (← mapFVarM f body) bi
  | .forallE arg ty body bi =>
    return .forallE arg (←mapFVarM f ty) (← mapFVarM f body) bi
  | .letE var ty value body nonDep  =>
    return .letE var (← mapFVarM f ty) (← mapFVarM f value) (← mapFVarM f body) nonDep
  | .bvar .. | .sort .. => return e
  | .mdata .. | .const .. | .lit .. => return e
  | .mvar .. => unreachable!

partial def Expr.forFVarM [Monad m] (f : FVarId → m Unit) (e : Expr) : m Unit := do
  match e with
  | .proj _ _ struct => forFVarM f struct
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
  | .letE _ ty value body ..  =>
    forFVarM f ty
    forFVarM f value
    forFVarM f body
  | .bvar .. | .sort .. => return
  | .mdata .. | .const .. | .lit .. => return
  | .mvar .. => unreachable!

instance : TraverseFVar Expr where
  mapFVarM := Expr.mapFVarM
  forFVarM := Expr.forFVarM

partial def LetDecl.mapFVarM [MonadLiftT CompilerM m] [Monad m] (f : FVarId → m FVarId) (decl : LetDecl) : m LetDecl := do
  decl.update (← Expr.mapFVarM f decl.type) (← Expr.mapFVarM f decl.value)

partial def LetDecl.forFVarM [Monad m] (f : FVarId → m Unit) (decl : LetDecl) : m Unit := do
  Expr.forFVarM f decl.type
  Expr.forFVarM f decl.value

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
    return Code.updateJmp! c (← f fn) (← args.mapM (Expr.mapFVarM f))
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
    args.forM (Expr.forFVarM f)
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


end Lean.Compiler.LCNF
