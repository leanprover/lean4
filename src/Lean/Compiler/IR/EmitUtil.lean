/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.InitAttr
public import Lean.Compiler.IR.CompilerM
import Lean.Compiler.NameMangling

public section

/-! # Helper functions for backend code generators -/

namespace Lean.IR

/-- Return true iff `b` is of the form `let x := g ys; ret x` -/
def isTailCallTo (g : Name) (b : FnBody) : Bool :=
  match b with
  | FnBody.vdecl x _ (Expr.fap f _) (FnBody.ret (.var y)) => x == y && f == g
  | _  => false

def usesModuleFrom (env : Environment) (modulePrefix : Name) : Bool :=
  env.allImportedModuleNames.toList.any fun modName => modulePrefix.isPrefixOf modName

/--
Wrapper around `IRType` where different object types are considered equal.
-/
structure IRTypeApprox where
  type : IRType

partial def IRType.hashApprox : IRType → UInt64
  | .float => 11
  | .uint8 => 13
  | .uint16 => 17
  | .uint32 => 19
  | .uint64 => 23
  | .usize => 29
  | .float32 => 31
  | .erased | .object | .tobject | .tagged | .void => 37
  | .struct _ tys us ss =>
    let : Hashable IRType := { hash := hashApprox }
    mixHash (mixHash (mixHash 41 (hash tys)) (hash us)) (hash ss)
  | .union _ tys =>
    let : Hashable IRType := { hash := hashApprox }
    mixHash 43 (hash tys)

instance : BEq IRTypeApprox := ⟨fun a b => a.type.compatibleWith b.type (strict := true)⟩
instance : Hashable IRTypeApprox := ⟨fun a => a.type.hashApprox⟩

structure StructTypeInfo where
  /-- The type itself after `normalizeObject`. -/
  type : IRType
  /-- The ids of struct types that this type can Reshape to. -/
  reshapes : Array Nat
deriving Inhabited

abbrev StructTypeData := Array StructTypeInfo
abbrev StructTypeLookup := Std.HashMap IRTypeApprox Nat

namespace CollectStructTypes

abbrev M := StateM (StructTypeData × StructTypeLookup)

partial def registerType (ty : IRType) : M Unit := do
  match ty with
  | .struct _ tys _ _ => tys.forM registerType
  | .union _ tys => tys.forM registerType
  | _ => return

  let (arr, map) ← get
  match map[IRTypeApprox.mk ty]? with
  | none =>
    let id := arr.size
    let ty := ty.normalizeObject
    modify fun m => (m.1.push ⟨ty, #[]⟩, m.2.insert ⟨ty⟩ id)
  | some _ => pure ()

def addReshapeEntry (origin target : IRType) : M Unit := do
  let id1 := (← get).2[IRTypeApprox.mk origin]!
  let id2 := (← get).2[IRTypeApprox.mk target]!
  modify fun m => (m.1.modify id1 fun info =>
    if info.reshapes.contains id2 then info
    else { info with reshapes := info.reshapes.push id2 }, m.2)

def addReshape (origin target : IRType) : M Unit := do
  match origin, target with
  | .struct _ tys _ _, .struct _ tys' _ _
  | .union _ tys, .union _ tys' =>
    for ty in tys, ty' in tys' do
      addReshape ty ty'
    addReshapeEntry origin target
  | _, _ => pure () -- ignore

def collectParams (params : Array Param) : M Unit := do
  for x in params do
    if x.ty.isStruct then
      registerType x.ty

partial def collectFnBody : FnBody → M Unit
  | .vdecl _ t v b => do
    if t.isStruct then
      registerType t
      match v with
      | .box t' _ => addReshape t' t
      | _ => pure ()
    collectFnBody b
  | .jdecl _ xs v b =>
    collectParams xs *> collectFnBody v *> collectFnBody b
  | .case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
  | e => do unless e.isTerminal do collectFnBody e.body

def collectDecl : Decl → M Unit
  | .fdecl _f xs ty b _ => collectParams xs *> registerType ty *> collectFnBody b
  | .extern _f xs ty _ => collectParams xs *> registerType ty

end CollectStructTypes

def collectStructTypes (decls : List Decl) : StructTypeData × StructTypeLookup :=
  ((decls.forM CollectStructTypes.collectDecl).run ({}, {})).2

namespace CollectUsedDecls

abbrev M := ReaderT Environment (StateM NameSet)

@[inline] def collect (f : FunId) : M Unit :=
  modify fun s => s.insert f

partial def collectFnBody : FnBody → M Unit
  | .vdecl _ _ v b   =>
    match v with
    | .fap f _ => collect f *> collectFnBody b
    | .pap f _ => collect f *> collectFnBody b
    | _        => collectFnBody b
  | .jdecl _ _ v b   => collectFnBody v *> collectFnBody b
  | .case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
  | e => do unless e.isTerminal do collectFnBody e.body

def collectInitDecl (fn : Name) : M Unit := do
  let env ← read
  match getInitFnNameFor? env fn with
  | some initFn => collect initFn
  | _           => pure ()

def collectDecl : Decl → M NameSet
  | .fdecl (f := f) (body := b) .. => collectInitDecl f *> CollectUsedDecls.collectFnBody b *> get
  | .extern (f := f) .. => collectInitDecl f *> get

end CollectUsedDecls

def collectUsedDecls (env : Environment) (decl : Decl) (used : NameSet := {}) : NameSet :=
  (CollectUsedDecls.collectDecl decl env).run' used

abbrev VarTypeMap  := Std.HashMap VarId IRType
abbrev JPParamsMap := Std.HashMap JoinPointId (Array Param)

namespace CollectMaps
abbrev Collector := (VarTypeMap × JPParamsMap) → (VarTypeMap × JPParamsMap)
@[inline] def collectVar (x : VarId) (t : IRType) : Collector
  | (vs, js) => (vs.insert x t, js)
def collectParams (ps : Array Param) : Collector :=
  fun s => ps.foldl (fun s p => collectVar p.x p.ty s) s
@[inline] def collectJP (j : JoinPointId) (xs : Array Param) : Collector
  | (vs, js) => (vs, js.insert j xs)

/-- `collectFnBody` assumes the variables in -/
partial def collectFnBody : FnBody → Collector
  | .vdecl x t _ b    => collectVar x t ∘ collectFnBody b
  | .jdecl j xs v b   => collectJP j xs ∘ collectParams xs ∘ collectFnBody v ∘ collectFnBody b
  | .case _ _ _ alts  => fun s => alts.foldl (fun s alt => collectFnBody alt.body s) s
  | e                 => if e.isTerminal then id else collectFnBody e.body

def collectDecl : Decl → Collector
  | .fdecl (xs := xs) (body := b) .. => collectParams xs ∘ collectFnBody b
  | _ => id

end CollectMaps

/-- Return a pair `(v, j)`, where `v` is a mapping from variable/parameter to type,
   and `j` is a mapping from join point to parameters.
   This function assumes `d` has normalized indexes (see `normids.lean`). -/
def mkVarJPMaps (d : Decl) : VarTypeMap × JPParamsMap :=
  CollectMaps.collectDecl d ({}, {})

end IR
end Lean
