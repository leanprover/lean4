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
def sortedBySize (pu : Purity) : Probe (Decl pu) (Nat × Decl pu) := fun decls =>
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

partial def getLetValues (pu : Purity) : Probe (Decl pu) (LetValue pu) := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (c : Code pu) : StateRefT (Array (LetValue pu)) CompilerM Unit := do
    match c with
    | .let decl k =>
      modify fun s => s.push decl.value
      go k
    | .fun decl k _ | .jp decl k =>
      go decl.value
      go k
    | .cases cs => cs.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()
    | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k
  start (decls : Array (Decl pu)) : StateRefT (Array (LetValue pu)) CompilerM Unit :=
    decls.forM (·.value.forCodeM go)

partial def getJps (pu : Purity) : Probe (Decl pu) (FunDecl pu) := fun decls => do
  let (_, res) ← start decls |>.run #[]
  return res
where
  go (code : Code pu) : StateRefT (Array (FunDecl pu)) CompilerM Unit := do
    match code with
    | .let _ k => go k
    | .fun decl k _ => go decl.value; go k
    | .jp decl k => modify (·.push decl); go decl.value; go k
    | .cases cs => cs.alts.forM (go ·.getCode)
    | .jmp .. | .return .. | .unreach .. => return ()
    | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

  start (decls : Array (Decl pu)) : StateRefT (Array (FunDecl pu)) CompilerM Unit :=
    decls.forM (·.value.forCodeM go)

partial def filterByLet (pu : Purity) (f : LetDecl pu → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let decl k => do if (← f decl) then return true else go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByFun (pu : Purity) (f : FunDecl pu → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k | .jp _ k  => go k
  | .fun decl k _ => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByJp (pu : Purity) (f : FunDecl pu → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ => go decl.value <||> go k
  | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByFunDecl (pu : Purity) (f : FunDecl pu → CompilerM Bool) :
    Probe (Decl pu) (Decl pu):=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => do if (← f decl) then return true else go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByCases (pu : Purity) (f : Cases pu → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => do if (← f cs) then return true else cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByJmp (pu : Purity) (f : FVarId → Array (Arg pu) → CompilerM Bool) :
    Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp fn var => f fn var
  | .return .. | .unreach .. => return false
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByReturn (pu : Purity) (f : FVarId → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .unreach .. => return false
  | .return var  => f var
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

partial def filterByUnreach (pu : Purity) (f : Expr → CompilerM Bool) : Probe (Decl pu) (Decl pu) :=
  filter (·.value.isCodeAndM go)
where
  go : Code pu → CompilerM Bool
  | .let _ k => go k
  | .fun decl k _ | .jp decl k => go decl.value <||> go k
  | .cases cs => cs.alts.anyM (go ·.getCode)
  | .jmp .. | .return .. => return false
  | .unreach typ  => f typ
  | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ => go k

@[inline]
def declNames (pu : Purity) : Probe (Decl pu) Name :=
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
