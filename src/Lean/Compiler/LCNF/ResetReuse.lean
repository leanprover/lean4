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

namespace Lean.Compiler.LCNF

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

mutual

/--
Given `Dmain x info b`, the resulting pair `(new_b, flag)` contains the new body `new_b`,
and `flag == true` if `x` is live in `b`.

Note that, in the function `D` defined in the paper, for each `let x := e; F`,
`D` checks whether `x` is live in `F` or not. This is great for clarity but it
is expensive: `O(n^2)` where `n` is the size of the function body. -/
partial def Dmain (x : FVarId) (info : CtorInfo) (k : Code .impure) : ReuseM (Code .impure × Bool) := do
  match k with
  | .cases cs =>
    if ← k.isFVarLiveIn x then
      /- If `x` is live in `e`, we recursively process each branch. -/
      let alts ← cs.alts.mapM fun alt => alt.mapCodeM fun b => D x info b
      return (k.updateAlts! alts, true)
    else
      return (k, false)
  | .jp decl k => sorry
  | .let decl k => sorry
  | .sset .. | .uset .. => sorry
  | .return .. | .jmp .. | .unreach .. =>
    return (k, ← k.isFVarLiveIn x)

partial def D (x : FVarId) (info : CtorInfo) (k : Code .impure) : ReuseM (Code .impure) :=
  sorry

end

/--
R from the paper
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
    let k ← k.insertResetReuse
    return c.updateFun! (← decl.updateValue value) k
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
      if decl.value matches .reset .. then
        modify fun s => s.insert decl.fvarId
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
