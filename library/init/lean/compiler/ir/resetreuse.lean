/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.state
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.freevars

namespace Lean
namespace IR
/- Remark: the insertResetReuse transformation is applied before we have
   inserted `inc/dec` instructions, and perfomed lower level optimizations
   that introduce the instructions `release` and `set`. -/

/- Remark: the functions `S`, `D` and `R` defined here implement the
  corresponding functions in the paper "Counting Immutable Beans"

  Here are the main differences:
  - We use the State monad to manage the generation of fresh variable names.
  - Support for join points, and `uset` and `sset` instructions for unboxed data.
  - `R` uses the `flatten` and `reshape` idiom.
  - `D` returns a pair `(b, found)` to avoid quadratic behavior when checking
    the last occurrence of the variable `x`
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
| (FnBody.jdecl j ys t v b) :=
  let v' := S v in
  if v == v' then FnBody.jdecl j ys t v (S b)
  else FnBody.jdecl j ys t v' b
| (FnBody.case tid x alts)  := FnBody.case tid x $ alts.hmap $ λ alt, alt.modifyBody S
| b :=
  if b.isTerminal then b
  else let
    (instr, b) := b.split in
    instr <;> S b

abbrev M := State Index
local attribute [instance] monadInhabited

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

private partial def Dmain (x : VarId) (c : CtorInfo) : FnBody → M (FnBody × Bool)
| b@(FnBody.case tid y alts) :=
  if b.hasFreeVar x then do
    alts ← alts.hmmap $ λ alt, alt.mmodifyBody (λ b, Dmain b >>= Dfinalize x c),
    pure (FnBody.case tid y alts, true)
  else
    pure (b, false)
| e :=
  if e.isTerminal then
    pure (e, e.hasFreeVar x)
  else do
    let (instr, b) := e.split,
    (b, found) ← Dmain b,
    if found || !instr.hasFreeVar x then
      pure (instr <;> b, found)
    else do
      b ← tryS x c b,
      pure (instr <;> b, true)

private partial def hasCtorUsing (x : VarId) : FnBody → Bool
| (FnBody.vdecl x _ (Expr.ctor _ ys) b) :=
  ys.any (λ arg, Arg.hasFreeVar arg x) || hasCtorUsing b
| b := !b.isTerminal && hasCtorUsing b.body

private def D (x : VarId) (c : CtorInfo) (b : FnBody) : M FnBody :=
/- If the scrutinee `x` (the one that is providing memory) is being
   stored in a constructor, then reuse will probably not work.
   It may work only if the new cell is consumed, but we ignore this case. -/
if hasCtorUsing x b then pure b
else Dmain x c b >>= Dfinalize x c

private partial def R : FnBody → M FnBody
| b := do
  let (bs, term) := b.flatten,
  bs ← mmodifyJPs bs R,
  match term with
  | FnBody.case tid x alts := do
    alts ← alts.hmmap $ λ alt, do {
      alt ← alt.mmodifyBody R,
      match alt with
      | Alt.ctor c b := Alt.ctor c <$> D x c b
      | _            := pure alt
    },
    let term := FnBody.case tid x alts,
    pure $ reshape bs term
  | other := pure $ reshape bs term

def Decl.insertResetReuse : Decl → Decl
| d@(Decl.fdecl f xs t b) :=
  let nextVar := d.maxVar + 1 in
  let b       := (R b).run' nextVar in
  Decl.fdecl f xs t b
| other := other

end IR
end Lean
