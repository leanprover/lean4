/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.LiveVars
import Lean.Compiler.IR.Format

namespace Lean.IR.ResetReuse
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

private def mayReuse (c₁ c₂ : CtorInfo) (relaxedReuse : Bool) : Bool :=
  c₁.size == c₂.size && c₁.usize == c₂.usize && c₁.ssize == c₂.ssize &&
  /- The following condition is a heuristic.
     If `relaxedReuse := false`, then we don't want to reuse cells from
     different constructors even when they are compatible
     because it produces counterintuitive behavior. -/
  (relaxedReuse || c₁.name.getPrefix == c₂.name.getPrefix)

/--
Replace `ctor` applications with `reuse` applications if compatible.
`w` contains the "memory cell" being reused.
-/
private partial def S (w : VarId) (c : CtorInfo) (relaxedReuse : Bool) (b : FnBody) : FnBody :=
  go b
where
  go : FnBody → FnBody
  | .vdecl x t v@(.ctor c' ys) b   =>
    if mayReuse c c' relaxedReuse then
      let updtCidx := c.cidx != c'.cidx
      .vdecl x t (.reuse w c' updtCidx ys) b
    else
      .vdecl x t v (go b)
  | .jdecl j ys v b   =>
    let v' := go v
    if v == v' then
      .jdecl j ys v (go b)
    else
      .jdecl j ys v' b
  | .case tid x xType alts =>
    .case tid x xType <| alts.map fun alt => alt.modifyBody go
  | b =>
    if b.isTerminal then
      b
    else
      let (instr, b) := b.split
      instr.setBody (go b)

structure Context where
  lctx      : LocalContext := {}
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
  alreadyFound : PHashSet VarId := {}
  /--
  If `relaxedReuse := true`, then allow memory cells from different
  constructors to be reused. For example, we can reuse a `PSigma.mk`
  to allocate a `Prod.mk`. To avoid counterintuitive behavior,
  we first try `relaxedReuse := false`, and then `relaxedReuse := true`.
  -/
  relaxedReuse : Bool := false

/-- We use `Context` to track join points in scope. -/
abbrev M := ReaderT Context (StateT Index Id)

private def mkFresh : M VarId := do
  let idx ← getModify fun n => n + 1
  return { idx := idx }

/--
Helper function for applying `S`. We only introduce a `reset` if we managed
to replace a `ctor` with `reuse` in `b`.
-/
private def tryS (x : VarId) (c : CtorInfo) (b : FnBody) : M FnBody := do
  let w ← mkFresh
  let b' := S w c (← read).relaxedReuse b
  if b == b' then
    return b
  else
    return .vdecl w IRType.object (.reset c.size x) b'

private def Dfinalize (x : VarId) (c : CtorInfo) : FnBody × Bool → M FnBody
  | (b, true)  => return b
  | (b, false) => tryS x c b

private def argsContainsVar (ys : Array Arg) (x : VarId) : Bool :=
  ys.any fun arg => match arg with
    | .var y => x == y
    | _      => false

private def isCtorUsing (b : FnBody) (x : VarId) : Bool :=
  match b with
  | .vdecl _ _ (.ctor _ ys) _ => argsContainsVar ys x
  | _ => false

/--
Given `Dmain b`, the resulting pair `(new_b, flag)` contains the new body `new_b`,
and `flag == true` if `x` is live in `b`.

Note that, in the function `D` defined in the paper, for each `let x := e; F`,
`D` checks whether `x` is live in `F` or not. This is great for clarity but it
is expensive: `O(n^2)` where `n` is the size of the function body. -/
private partial def Dmain (x : VarId) (c : CtorInfo) (e : FnBody) : M (FnBody × Bool) := do
  match e with
  | .case tid y yType alts =>
    if e.hasLiveVar (← read).lctx x then
      /- If `x` is live in `e`, we recursively process each branch. -/
      let alts ← alts.mapM fun alt => alt.mmodifyBody fun b => Dmain x c b >>= Dfinalize x c
      return (.case tid y yType alts, true)
    else
      return (e, false)
  | .jdecl j ys v b =>
    let (b, found) ← withReader (fun ctx => { ctx with lctx := ctx.lctx.addJP j ys v }) (Dmain x c b)
    let (v, _ /- found' -/) ← Dmain x c v
    /- If `found' == true`, then `Dmain b` must also have returned `(b, true)` since
       we assume the IR does not have dead join points. So, if `x` is live in `j` (i.e., `v`),
       then it must also live in `b` since `j` is reachable from `b` with a `jmp`.
       On the other hand, `x` may be live in `b` but dead in `j` (i.e., `v`). -/
    return (.jdecl j ys v b, found)
  | e =>
    if e.isTerminal then
      return (e, e.hasLiveVar (← read).lctx x)
    else do
      let (instr, b) := e.split
      if isCtorUsing instr x then
        /- If the scrutinee `x` (the one that is providing memory) is being
           stored in a constructor, then reuse will probably not be able to reuse memory at runtime.
           It may work only if the new cell is consumed, but we ignore this case. -/
        return (e, true)
      else
        let (b, found) ← Dmain x c b
        /- Remark: it is fine to use `hasFreeVar` instead of `hasLiveVar`
           since `instr` is not a `FnBody.jmp` (it is not a terminal) nor
           it is a `FnBody.jdecl`. -/
        if found || !instr.hasFreeVar x then
          return (instr.setBody b, found)
        else
          let b ← tryS x c b
          return (instr.setBody b, true)

private def D (x : VarId) (c : CtorInfo) (b : FnBody) : M FnBody :=
  Dmain x c b >>= Dfinalize x c

partial def R (e : FnBody) : M FnBody := do
  match e with
  | .case tid x xType alts =>
    let alreadyFound := (← read).alreadyFound.contains x
    withReader (fun ctx => { ctx with alreadyFound := ctx.alreadyFound.insert x }) do
      let alts ← alts.mapM fun alt => do
        let alt ← alt.mmodifyBody R
        match alt with
        | .ctor c b =>
          if c.isScalar || alreadyFound then
            -- If `alreadyFound`, then we don't try to reuse memory cell to avoid
            -- double reset.
            return alt
          else
            .ctor c <$> D x c b
        | _ => return alt
      return .case tid x xType alts
  | .jdecl j ys v b =>
    let v ← R v
    let b ← withReader (fun ctx => { ctx with lctx := ctx.lctx.addJP j ys v }) (R b)
    return .jdecl j ys v b
  | e =>
    if e.isTerminal then
      return e
    else
      let (instr, b) := e.split
      let b ← R b
      return instr.setBody b

abbrev N := StateT (PHashSet VarId) Id

partial def collectResets (e : FnBody) : N Unit := do
  match e with
  | .case _ _ _ alts => alts.forM fun alt => collectResets alt.body
  | .jdecl _ _ v b => collectResets v; collectResets b
  | .vdecl _ _ (.reset _ x) b => modify fun s => s.insert x; collectResets b
  | e => unless e.isTerminal do
    let (_, b) := e.split
    collectResets b

end ResetReuse
open ResetReuse


def Decl.insertResetReuseCore (d : Decl) (relaxedReuse : Bool) : Decl :=
  match d with
  | .fdecl (body := b) .. =>
    let nextIndex := d.maxIndex + 1
    -- First time we execute `insertResetReuseCore`, `relaxedReuse := false`.
    let alreadyFound : PHashSet VarId := if relaxedReuse then (collectResets b *> get).run' {} else {}
    let bNew := R b { relaxedReuse, alreadyFound } |>.run' nextIndex
    d.updateBody! bNew
  | other => other

def Decl.insertResetReuse (d : Decl) : Decl :=
  /-
  We execute the reset/reuse algorithm twice. The first time, we only reuse memory cells
  between identical constructor memory cells. That is, we do not reuse a `PSigma.mk` memory cell
  when allocating a `Prod.mk` memory cell, even though they have the same layout. Recall
  that the reset/reuse placement algorithm is a heuristic, and the first pass prevents reuses
  that are unlikely to be useful at runtime. Then, we run the procedure again,
  relaxing this restriction. If there are still opportunities for reuse, we will take advantage of them.

  The second pass addresses issue #4089.
  -/
  d.insertResetReuseCore (relaxedReuse := false)
  |>.insertResetReuseCore (relaxedReuse := true)

end Lean.IR
