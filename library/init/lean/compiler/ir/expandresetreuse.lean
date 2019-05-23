/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.state
import init.control.reader
import init.lean.compiler.ir.compilerm

namespace Lean
namespace IR
namespace ExpandResetReuse

/- Return true iff `x` is consumed in all branches of the current block.
   Here consumption means the block contains a `dec x` or `reuse x ...`. -/
partial def consumed (x : VarId) : FnBody → Bool
| (FnBody.vdecl _ _ v b) :=
  match v with
  | Expr.reuse y _ _ _   := x == y || consumed b
  | _                    := consumed b
| (FnBody.dec y _ _ b)   := x == y || consumed b
| (FnBody.case _ _ alts) := alts.any $ λ alt, consumed alt.body
| e := !e.isTerminal && consumed e.body

partial def expand (bs : Array FnBody) (x : VarId) (n : Nat) (y : VarId) (b : FnBody) : FnBody :=
-- dbgTrace ("FOUND " ++ toString x) $ λ _,
reshape bs (FnBody.vdecl x IRType.object (Expr.reset n y) b)

partial def searchAndExpand : FnBody → Array FnBody → FnBody
| d@(FnBody.vdecl x t (Expr.reset n y) b) bs :=
  if consumed x b then
    expand bs x n y b
  else
    searchAndExpand b (push bs d)
| (FnBody.case tid x alts) bs :=
  let alts := alts.hmap $ λ alt, alt.modifyBody $ λ b, searchAndExpand b Array.empty in
  reshape bs (FnBody.case tid x alts)
| b bs :=
  if b.isTerminal then reshape bs b
  else searchAndExpand b.body (push bs b)

end ExpandResetReuse

/-- (Try to) expand `reset` and `reuse` instructions. -/
def Decl.expandResetReuse : Decl → Decl
| (Decl.fdecl f xs t b) := Decl.fdecl f xs t (ExpandResetReuse.searchAndExpand b Array.empty)
| other                 := other

end IR
end Lean
