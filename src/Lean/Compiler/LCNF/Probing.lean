/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.PhaseExt

public section

namespace Lean.Compiler.LCNF

abbrev Probe α β := Array α → CompilerM (Array β)

namespace Probe

@[inline]
def map (f : α → CompilerM β) : Probe α β := fun data => data.mapM f

@[inline]
def filter (f : α → CompilerM Bool) : Probe α α := fun data => data.filterM f

@[inline]
def sorted [Inhabited α] [LT α] [DecidableLT α] : Probe α α := fun data => return data.qsort (· < ·)

@[inline]
def sortedBySize (ph : Purity) : Probe (Decl ph) (Nat × Decl ph) := fun decls =>
  let decls := decls.map fun decl => (decl.size, decl)
  return decls.qsort fun (sz₁, decl₁) (sz₂, decl₂) =>
    if sz₁ == sz₂ then Name.lt decl₁.name decl₂.name else sz₁ < sz₂

def countUnique [ToString α] [BEq α] [Hashable α] : Probe α (α × Nat) := fun data => do
  let mut map := Std.HashMap.emptyWithCapacity data.size
  for d in data do
    if let some count := map[d]? then
      map := map.insert d (count + 1)
    else
      map := map.insert d 1
  return map.toArray

@[inline]
def countUniqueSorted [ToString α] [BEq α] [Hashable α] [Inhabited α] : Probe α (α × Nat) :=
  countUnique >=> fun data => return data.qsort (fun l r => l.snd < r.snd)

partial def getLetValues (ph : Purity) : Probe (Decl ph) (LetValue ph) := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (c : Code ph) : StateRefT (Array (LetValue ph)) CompilerM Unit := do
    match c with
    | .let decl k =>
      modify fun s => s.push decl.value
      go k
    | .fun decl k _ | .jp decl k =>
      go decl.value
      go k
    | .cases cs => cs.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()
  start (decls : Array (Decl ph)) : StateRefT (Array (LetValue ph)) CompilerM Unit :=
    decls.forM (·.value.forCodeM go)

partial def getJps (ph : Purity) : Probe (Decl ph) (FunDecl ph) := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (code : Code ph) : StateRefT (Array (FunDecl ph)) CompilerM Unit := do
    match code with
    | .let _ k => go k
    | .fun decl k _ => go decl.value; go k
    | .jp decl k => modify (·.push decl); go decl.value; go k
    | .cases cs => cs.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()

  start (decls : Array (Decl ph)) : StateRefT (Array (FunDecl ph)) CompilerM Unit :=
    decls.forM (·.value.forCodeM go)

partial def filterByLet (ph : Purity) (f : LetDecl ph → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let decl k => do if (← f decl) then return true else go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByFun (ph : Purity) (f : FunDecl ph → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k | .jp _ k  => go k
  | .fun decl k _ => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByJp (ph : Purity) (f : FunDecl ph → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ => go decl.value <||> go k
  | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByFunDecl (ph : Purity) (f : FunDecl ph → CompilerM Bool) :
    Probe (Decl ph) (Decl ph):=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByCases (ph : Purity) (f : Cases ph → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => do if (← f cs) then return true else cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByJmp (ph : Purity) (f : FVarId → Array (Arg ph) → CompilerM Bool) :
    Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp fn var => f fn var
  | .return .. | .unreach .. => return false

partial def filterByReturn (ph : Purity) (f : FVarId → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .unreach .. => return false
  | .return var  => f var

partial def filterByUnreach (ph : Purity) (f : Expr → CompilerM Bool) : Probe (Decl ph) (Decl ph) :=
  filter (·.value.isCodeAndM go)
where
  go : Code ph → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. => return false
  | .unreach typ  => f typ

@[inline]
def declNames (ph : Purity) : Probe (Decl ph) Name :=
  Probe.map (fun decl => return decl.name)

@[inline]
def toString [ToString α] : Probe α String :=
  Probe.map (return ToString.toString ·)

@[inline]
def count : Probe α Nat := fun data => return #[data.size]

@[inline]
def sum : Probe Nat Nat := fun data => return #[data.foldl (init := 0) (·+·)]

@[inline]
def tail (n : Nat) : Probe α α := fun data => return data[(data.size - n)...*]

@[inline]
def head (n : Nat) : Probe α α := fun data => return data[*...n]

def runOnDeclsNamed (declNames : Array Name) (phase : Phase := Phase.base)
    (probe : Probe (Decl phase.toPurity) β) : CoreM (Array β) := do
  let ext := getExt phase
  let env ← getEnv
  let decls ← declNames.mapM fun name => do
    let some decl := getDeclCore? env ext name | throwError "decl `{name}` not found"
    return decl
  probe decls |>.run (phase := phase)

def runOnModule (moduleName : Name) (phase : Phase := Phase.base)
    (probe : Probe (Decl phase.toPurity) β) : CoreM (Array β) := do
  let ext := getExt phase
  let env ← getEnv
  let some modIdx := env.getModuleIdx? moduleName | throwError "module `{moduleName}` not found"
  let decls := ext.getModuleEntries env modIdx
  probe decls |>.run (phase := phase)

def runGlobally  (phase : Phase := Phase.base) (probe : Probe (Decl phase.toPurity) β) : CoreM (Array β) := do
  let ext := getExt phase
  let env ← getEnv
  let mut decls := #[]
  for modIdx in *...env.allImportedModuleNames.size do
    decls := decls.append <| ext.getModuleEntries env modIdx
  probe decls |>.run (phase := phase)

def toPass [ToString β] (phase : Phase) (probe : Probe (Decl phase.toPurity) β) : Pass where
  phase := phase
  name := `probe
  run := fun decls => do
    let res ← probe decls
    trace[Compiler.probe] s!"{res}"
    return decls

builtin_initialize
  registerTraceClass `Compiler.probe (inherited := true)

end Probe

end Lean.Compiler.LCNF
