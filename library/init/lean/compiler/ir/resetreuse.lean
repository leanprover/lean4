/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.state
import init.control.reader
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.livevars

namespace Lean
namespace IR
namespace ResetReuse
/- Remark: the insertResetReuse transformation is applied before we have
   inserted `inc/dec` instructions, and perfomed lower level optimizations
   that introduce the instructions `release` and `set`. -/

/- Remark: the functions `S`, `D` and `R` defined here implement the
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

private def mayReuse (c₁ c₂ : CtorInfo) : Bool :=
c₁.size == c₂.size && c₁.usize == c₂.usize && c₁.ssize == c₂.ssize &&
/- The following condition is a heuristic.
   We don't want to reuse cells from different types even when they are compatible
   because it produces counterintuitive behavior. -/
c₁.name.getPrefix == c₂.name.getPrefix

private partial def S (w : VarId) (c : CtorInfo) : FnBody → FnBody
| (FnBody.vdecl x t v@(Expr.ctor c' ys) b) :=
  if mayReuse c c' then
    let updtCidx := c.cidx != c'.cidx in
    FnBody.vdecl x t (Expr.reuse w c updtCidx ys) b
  else
    FnBody.vdecl x t v (S b)
| (FnBody.jdecl j ys v b) :=
  let v' := S v in
  if v == v' then FnBody.jdecl j ys v (S b)
  else FnBody.jdecl j ys v' b
| (FnBody.case tid x alts)  := FnBody.case tid x $ alts.hmap $ λ alt, alt.modifyBody S
| b :=
  if b.isTerminal then b
  else let
    (instr, b) := b.split in
    instr <;> S b

/- We use `Context` to track join points in scope. -/
abbrev M := ReaderT LocalContext (StateT Index Id)

private def mkFresh : M VarId :=
do idx ← getModify (+1),
   pure { idx := idx }

private def tryS (x : VarId) (c : CtorInfo) (b : FnBody) : M FnBody :=
do w ← mkFresh,
   let b' := S w c b in
   if b == b' then pure b
   else pure $ FnBody.vdecl w IRType.object (Expr.reset x) b'

private def Dfinalize (x : VarId) (c : CtorInfo) : FnBody × Bool → M FnBody
| (b, true)  := pure b
| (b, false) := tryS x c b

/- Given `Dmain b`, the resulting pair `(new_b, flag)` contains the new body `new_b`,
   and `flag == true` if `x` is live in `b`.

   Note that, in the function `D` defined in the paper, for each `let x := e; F`,
   `D` checks whether `x` is live in `F` or not. This is great for clarity but it
   is expensive: `O(n^2)` where `n` is the size of the function body. -/
private partial def Dmain (x : VarId) (c : CtorInfo) : FnBody → M (FnBody × Bool)
| e@(FnBody.case tid y alts) := do
  ctx ← read,
  if e.hasLiveVar ctx x then do
    /- If `x` is live in `e`, we recursively process each branch. -/
    alts ← alts.hmmap $ λ alt, alt.mmodifyBody (λ b, Dmain b >>= Dfinalize x c),
    pure (FnBody.case tid y alts, true)
  else pure (e, false)
| (FnBody.jdecl j ys v b) := do
  (b, _) ← adaptReader (λ ctx : LocalContext, ctx.addJP j ys v) (Dmain b),
  (v, found) ← Dmain v,
  /- If `found == true`, then `Dmain b` must also have returned `(b, true)` since
     we assume the IR does not have dead join points. So, if `x` is live in `j`,
     then it must also live in `b` since `j` is reachable from `b` with a `jmp`. -/
  pure (FnBody.jdecl j ys v b, found)
| e := do
  ctx ← read,
  if e.isTerminal then
    pure (e, e.hasLiveVar ctx x)
  else do
    let (instr, b) := e.split,
    (b, found) ← Dmain b,
    /- Remark: it is fine to use `hasFreeVar` instead of `hasLiveVar`
       since `instr` is not a `FnBody.jmp` (it is not a terminal) nor it is a `FnBody.jdecl`. -/
    if found || !instr.hasFreeVar x then
      pure (instr <;> b, found)
    else do
      b ← tryS x c b,
      pure (instr <;> b, true)

/- Auxiliary function used to implement an additional heuristic at `D`. -/
private partial def hasCtorUsing (x : VarId) : FnBody → Bool
| (FnBody.vdecl x _ (Expr.ctor _ ys) b) :=
  ys.any (λ arg, match arg with
           | Arg.var y := x == y
           | _         := false)
  || hasCtorUsing b
| (FnBody.jdecl _ _ v b) := hasCtorUsing v || hasCtorUsing b
| b                      := !b.isTerminal && hasCtorUsing b.body

private def D (x : VarId) (c : CtorInfo) (b : FnBody) : M FnBody :=
/- If the scrutinee `x` (the one that is providing memory) is being
   stored in a constructor, then reuse will probably not be able to reuse memory at runtime.
   It may work only if the new cell is consumed, but we ignore this case. -/
if hasCtorUsing x b then pure b
else Dmain x c b >>= Dfinalize x c

partial def R : FnBody → M FnBody
| (FnBody.case tid x alts) := do
    alts ← alts.hmmap $ λ alt, do {
      alt ← alt.mmodifyBody R,
      match alt with
      | Alt.ctor c b :=
        if c.isScalar then pure alt
        else Alt.ctor c <$> D x c b
      | _            := pure alt
    },
    pure $ FnBody.case tid x alts
| (FnBody.jdecl j ys v b) := do
  v ← R v,
  b ← adaptReader (λ ctx : LocalContext, ctx.addJP j ys v) (R b),
  pure $ FnBody.jdecl j ys v b
| e := do
  if e.isTerminal then pure e
  else do
    let (instr, b) := e.split,
    b ← R b,
    pure (instr <;> b)

end ResetReuse

open ResetReuse

def Decl.insertResetReuse : Decl → Decl
| d@(Decl.fdecl f xs t b) :=
  let nextIndex := d.maxIndex + 1 in
  let b         := (R b {}).run' nextIndex in
  Decl.fdecl f xs t b
| other := other

end IR
end Lean
