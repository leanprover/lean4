/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.LiveVars
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.IR.CompilerM

namespace Lean.Compiler.LCNF

/-!
Remark: the insertResetReuse transformation is applied before we have
inserted `inc/dec` instructions, and performed lower level optimizations
that introduce the instructions `release` and `set`.
-/

/-!
Remark: the functions `S`, `D` and `R` defined here implement the
corresponding functions in the paper "Counting Immutable Beans"

Here are the main differences:
- We use the State monad to manage the generation of fresh variable names.
- Support for join points, and `uset` and `sset` instructions for unboxed data.
- `D` uses the auxiliary function `Dmain`.
- `Dmain` returns a pair `(b, found)` to avoid quadratic behavior when checking
  the last occurrence of the variable `x`.
- Because we have join points in the actual implementation, a variable may be live even if it
  does not occur in a function body. See example at `livevars.lean`.
-/

structure Context where
  /--
  Contains all variables in `cases` statements in the current path
  and variables that are already in `reset` statements when we
  invoke `R`.

  We use this information to prevent double-reset in code such as
  ```
  case x_i : obj of
  Prod.mk →
    case x_i : obj of
    Prod.mk →
    ...
  ```

  A variable can already be in a `reset` statement when we
  invoke `R` because we execute it with and without `relaxedReuse`.
  -/
  alreadyFound : PersistentHashSet FVarId := {}
  /--
  If `relaxedReuse := true`, then allow memory cells from different
  constructors to be reused. For example, we can reuse a `PSigma.mk`
  to allocate a `Prod.mk`. To avoid counterintuitive behavior,
  we first try `relaxedReuse := false`, and then `relaxedReuse := true`.
  -/
  relaxedReuse : Bool

abbrev ReuseM := ReaderT Context CompilerM

def mayReuse (c₁ c₂ : CtorInfo) : ReuseM Bool :=
  return c₁.size == c₂.size && c₁.usize == c₂.usize && c₁.ssize == c₂.ssize &&
  /- The following condition is a heuristic.
     If `relaxedReuse := false`, then we don't want to reuse cells from
     different constructors even when they are compatible
     because it produces counterintuitive behavior. -/
  ((← read).relaxedReuse || c₁.name.getPrefix == c₂.name.getPrefix)

/--
Replace `ctor` applications with `reuse` applications if compatible.
`w` contains the "memory cell" being reused.
-/
partial def S (w : FVarId) (info : CtorInfo) (b : Code .impure) :
    ReuseM (Code .impure × Bool) :=
  go b
where
  go (c : Code .impure) : ReuseM (Code .impure × Bool) := do
    let goK (k : Code .impure) : ReuseM (Code .impure × Bool) := do
      let (k, changed) ← go k
      return (c.updateCont! k, changed)
    match c with
    | .let decl@{ value := .ctor info' ys _, .. } k =>
      if ← mayReuse info info' then
        let updateNecessary := info.cidx != info'.cidx
        let code := .let (← decl.update decl.type (.reuse w info' updateNecessary ys)) k
        return (code, true)
      else
        goK k
    | .jp decl k =>
      let (value, changed) ← go decl.value
      if changed then
        return (c.updateFun! (← decl.updateValue value) k, changed)
      else
        goK k
    | .cases cs =>
      let result ← cs.alts.mapM fun alt => do
        let (altCode, changed) ← go alt.getCode
        return (alt.updateCode altCode, changed)
      let (alts, altsChanged) := result.unzip
      return (c.updateAlts! alts, altsChanged.any id)
    | .return .. | .jmp .. | .unreach .. => return (c, false)
    | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ | .let _ k =>
      goK k

def tryS (x : FVarId) (info : CtorInfo) (b : Code .impure) : ReuseM (Code .impure) := do
  let w ← mkFreshFVarId
  let (b', changed) ← S w info b
  if changed then
    let decl := { fvarId := w, binderName := (← mkFreshBinderName `_x), type := ImpureType.tobject, value := .reset info.size x }
    modifyLCtx fun lctx => lctx.addLetDecl decl
    return .let decl b'
  else
    return b

def isCtorUsing (b : CodeDecl .impure) (x : FVarId) : Bool :=
  match b with
  | .let { value := .ctor _ args _, .. } => args.any (·.dependsOn { x })
  | _ => false

-- TODO document
inductive UseClassification where
  | ownedArg
  | other
  | none

def classifyUse (b : CodeDecl .impure) (x : FVarId) : ReuseM UseClassification := do
  match b with
  | .let { value := e@(.fap f args _), .. } =>
    -- TODO: change this to getImpureSignature in later refactoring phases
    if let some decl := IR.findEnvDecl (← getEnv) f then
      let mut result := .none
      for arg in args, param in decl.params do
        if let .fvar y := arg then
          if y == x then
            result :=
              match result, param.borrow with
              | .ownedArg, true => .other
              | .ownedArg, false => .ownedArg
              | .other, _ => .other
              | .none, true => .other
              | .none, false => .ownedArg
      return result
    else
      if e.dependsOn { x } then
        return .ownedArg
      else
        return .none
  | .let { value := e@(.pap ..), .. } | .let { value := e@(.fvar ..), .. } =>
    if e.dependsOn { x } then
      return .ownedArg
    else
      return .none
  | _ =>
    if b.dependsOn { x } then
      return .other
    else
      return .none


mutual

partial def Dfinalize (x : FVarId) (info : CtorInfo) : Code .impure × Bool → ReuseM (Code .impure)
  | (b, true) => return b
  | (b, false) => tryS x info b

/--
Given `Dmain x info c`, the resulting pair `(newC, flag)` contains the new body `newC`,
and `flag == true` if `x` is live in `b`.

Note that, in the function `D` defined in the paper, for each `let x := e; F`,
`D` checks whether `x` is live in `F` or not. This is great for clarity but it
is expensive: `O(n^2)` where `n` is the size of the function body.
-/
partial def Dmain (x : FVarId) (info : CtorInfo) (c : Code .impure) : ReuseM (Code .impure × Bool) := do
  match c with
  | .cases cs =>
    if ← c.isFVarLiveIn x then
      /- If `x` is live in `e`, we recursively process each branch. -/
      let alts ← cs.alts.mapM fun alt => alt.mapCodeM fun b => D x info b
      return (c.updateAlts! alts, true)
    else
      return (c, false)
  | .jp decl k =>
    let (k, found) ← Dmain x info k
    let (value, _ /- found' -/ ) ← Dmain x info decl.value
    /- If `found' == true`, then `Dmain k` must also have returned `(b, true)` since
       we assume the IR does not have dead join points. So, if `x` is live in `j` (i.e., `v`),
       then it must also live in `b` since `j` is reachable from `b` with a `jmp`.
       On the other hand, `x` may be live in `b` but dead in `j` (i.e., `v`). -/
    return (c.updateFun! (← decl.updateValue value) k, found)
  | .let _ k | .sset _ _ _ _ _ k _ | .uset _ _ _ k _ =>
    let instr := c.toCodeDecl!
    if isCtorUsing instr x then
      /- If the scrutinee `x` (the one that is providing memory) is being
         stored in a constructor, then reuse will probably not be able to reuse memory at runtime.
         It may work only if the new cell is consumed, but we ignore this case. -/
      return (c, true)
    else
      let (k, found) ← Dmain x info k
      if found then
        return (c.updateCont! k, true)
      else
        match (← classifyUse instr x) with
        | .ownedArg =>
          return (c.updateCont! k, true)
        | .other =>
          let k ← tryS x info k
          return (c.updateCont! k, true)
        | .none =>
          return (c.updateCont! k, false)
  | .return .. | .jmp .. | .unreach .. =>
    return (c, ← c.isFVarLiveIn x)

/--
This function corresponds to `D` from the paper. It looks for positions in `k` where `x` is not live
anymore and then invokes `S` to look for reuse opportunities after these positions.
-/
partial def D (x : FVarId) (info : CtorInfo) (k : Code .impure) : ReuseM (Code .impure) :=
  Dmain x info k >>= Dfinalize x info

end

/--
This function corresponds to `R` from the paper. It searches for and inserts reset-reuse
opportunities into `c`.
-/
partial def Code.insertResetReuse (c : Code .impure) : ReuseM (Code .impure) := do
  match c with
  | .cases cs =>
    let alreadyFound := (← read).alreadyFound.contains cs.discr
    withReader (fun ctx => { ctx with alreadyFound := ctx.alreadyFound.insert cs.discr }) do
      let alts ← cs.alts.mapM fun alt => do
        let alt ← alt.mapCodeM (·.insertResetReuse)
        match alt with
        | .ctorAlt info k =>
          if info.isScalar || alreadyFound then
            -- If `alreadyFound`, then we don't try to reuse memory cell to avoid
            -- double reset.
            return alt
          else
            return alt.updateCode (← D cs.discr info k)
        | .default .. => return alt
      return c.updateAlts! alts
  | .jp decl k =>
    let value ← decl.value.insertResetReuse
    let decl ← decl.updateValue value
    let k ← k.insertResetReuse
    return c.updateFun! decl k
  | .let _ k | .uset _ _ _ k _ | .sset _ _ _ _ _ k _  =>
    return c.updateCont! (← k.insertResetReuse)
  | .return .. | .jmp .. | .unreach .. => return c

partial def Decl.insertResetReuseCore (decl : Decl .impure) : ReuseM (Decl .impure) := do
  let value ← decl.value.mapCodeM fun code => do
    let alreadyFound ←
      if (← read).relaxedReuse then
        pure (← (collectResets code).run {}).snd
      else
        pure {}
    withReader (fun ctx => { ctx with alreadyFound }) do
      code.insertResetReuse
  return { decl with value }
where
  collectResets (c : Code .impure) : StateRefT (PersistentHashSet FVarId) CompilerM Unit := do
    match c with
    | .let decl k =>
      if let .reset _ var := decl.value then
        modify fun s => s.insert var
      collectResets k
    | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ => collectResets k
    | .jp decl k => collectResets decl.value; collectResets k
    | .cases c => c.alts.forM (collectResets ·.getCode)
    | .unreach .. | .return .. | .jmp .. => return ()


def Decl.insertResetReuse (decl : Decl .impure) : CompilerM (Decl .impure) := do
  /-
  We execute the reset/reuse algorithm twice. The first time, we only reuse memory cells
  between identical constructor memory cells. That is, we do not reuse a `PSigma.mk` memory cell
  when allocating a `Prod.mk` memory cell, even though they have the same layout. Recall
  that the reset/reuse placement algorithm is a heuristic, and the first pass prevents reuses
  that are unlikely to be useful at runtime. Then, we run the procedure again,
  relaxing this restriction. If there are still opportunities for reuse, we will take advantage of them.

  The second pass addresses issue #4089.
  -/
  if (← getConfig).resetReuse then
    let decl ← decl.insertResetReuseCore |>.run { relaxedReuse := false }
    decl.insertResetReuseCore |>.run { relaxedReuse := true }
  else
    return decl

public def insertResetReuse : Pass :=
  Pass.mkPerDeclaration `resetReuse .impure Decl.insertResetReuse 0

builtin_initialize
  registerTraceClass `Compiler.resetReuse (inherited := true)

end Lean.Compiler.LCNF
