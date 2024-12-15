/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PhaseExt

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
def sortedBySize : Probe Decl (Nat × Decl) := fun decls =>
  let decls := decls.map fun decl => (decl.size, decl)
  return decls.qsort fun (sz₁, decl₁) (sz₂, decl₂) =>
    if sz₁ == sz₂ then Name.lt decl₁.name decl₂.name else sz₁ < sz₂

def countUnique [ToString α] [BEq α] [Hashable α] : Probe α (α × Nat) := fun data => do
  let mut map := Std.HashMap.empty
  for d in data do
    if let some count := map[d]? then
      map := map.insert d (count + 1)
    else
      map := map.insert d 1
  return map.toArray

@[inline]
def countUniqueSorted [ToString α] [BEq α] [Hashable α] [Inhabited α] : Probe α (α × Nat) :=
  countUnique >=> fun data => return data.qsort (fun l r => l.snd < r.snd)

partial def getLetValues : Probe Decl LetValue := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (c : Code) : StateRefT (Array LetValue) CompilerM Unit := do
    match c with
    | .let (decl : LetDecl) (k : Code) =>
      modify fun s => s.push decl.value
      go k
    | .fun decl k | .jp decl k =>
      go decl.value
      go k
    | .cases (cases : CasesCore Code) => cases.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()
  start (decls : Array Decl) : StateRefT (Array LetValue) CompilerM Unit :=
    decls.forM (go ·.value)

partial def getJps : Probe Decl FunDecl := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (code : Code) : StateRefT (Array FunDecl) CompilerM Unit := do
    match code with
    | .let _ k => go k
    | .fun decl k => go decl.value; go k
    | .jp decl k => modify (·.push decl); go decl.value; go k
    | .cases cs => cs.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()

  start (decls : Array Decl) : StateRefT (Array FunDecl) CompilerM Unit :=
    decls.forM fun decl => go decl.value

partial def filterByLet (f : LetDecl → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let decl k => do if (← f decl) then return true else go k
  | .fun decl k | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByFun (f : FunDecl → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k | .jp _ k  => go k
  | .fun decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByJp (f : FunDecl → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k => go decl.value <||> go k
  | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByFunDecl (f : FunDecl → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByCases (f : Cases → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k | .jp decl k => go decl.value <||> go k
  | .cases cs => do if (← f cs) then return true else cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false

partial def filterByJmp (f : FVarId → Array Arg → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp fn var => f fn var
  | .return .. | .unreach .. => return false

partial def filterByReturn (f : FVarId → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .unreach .. => return false
  | .return var  => f var

partial def filterByUnreach (f : Expr → CompilerM Bool) : Probe Decl Decl :=
  filter (fun decl => go decl.value)
where
  go : Code → CompilerM Bool
  | .let _ k => go k
  | .fun decl k | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. => return false
  | .unreach typ  => f typ

@[inline]
def declNames : Probe Decl Name :=
  Probe.map (fun decl => return decl.name)

@[inline]
def toString [ToString α] : Probe α String :=
  Probe.map (return ToString.toString ·)

@[inline]
def count : Probe α Nat := fun data => return #[data.size]

@[inline]
def sum : Probe Nat Nat := fun data => return #[data.foldl (init := 0) (·+·)]

@[inline]
def tail (n : Nat) : Probe α α := fun data => return data[data.size - n:]

@[inline]
def head (n : Nat) : Probe α α := fun data => return data[:n]

def runOnModule (moduleName : Name) (probe : Probe Decl β) (phase : Phase := Phase.base): CoreM (Array β) := do
  let ext := getExt phase
  let env ← getEnv
  let some modIdx := env.getModuleIdx? moduleName | throwError "module `{moduleName}` not found"
  let decls := ext.getModuleEntries env modIdx
  probe decls |>.run (phase := phase)

def runGlobally (probe : Probe Decl β) (phase : Phase := Phase.base) : CoreM (Array β) := do
  let ext := getExt phase
  let env ← getEnv
  let mut decls := #[]
  for modIdx in [:env.allImportedModuleNames.size] do
    decls := decls.append <| ext.getModuleEntries env modIdx
  probe decls |>.run (phase := phase)

def toPass [ToString β] (probe : Probe Decl β) (phase : Phase) : Pass where
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
