/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.Occurrences
import Lean.HeadIndex
import Lean.Meta.Basic

namespace Lean.Meta

/--
Abstract occurrences of `p` in `e`. We detect subterms equivalent to `p` using key-matching.
That is, only perform `isDefEq` tests when the head symbol of substerm is equivalent to head symbol of `p`.
By default, all occurrences are abstracted, but this behavior can be controlled using the `occs` parameter.
-/
def kabstract (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
      let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
        match e with
        | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
        | .mdata _ b       => return e.updateMData! (← visit b offset)
        | .proj _ _ b      => return e.updateProj! (← visit b offset)
        | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
        | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
        | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
        | e                => return e
      if e.hasLooseBVars then
        visitChildren ()
      else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
        visitChildren ()
      else if (← isDefEq e p) then
        let i ← get
        set (i+1)
        if occs.contains i then
          return mkBVar offset
        else
          visitChildren ()
      else
        visitChildren ()
    visit e 0 |>.run' 1

end Lean.Meta
