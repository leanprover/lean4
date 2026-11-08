/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Lean.HeadIndex
public import Lean.Meta.Basic

public section

namespace Lean.Meta

/--
Abstract occurrences of `p` in `e`. We detect subterms equivalent to `p` using key-matching.
That is, only perform `isDefEq` tests when the head symbol of subterm is equivalent to head symbol of `p`.

By default, all occurrences are abstracted,
but this behavior can be controlled using the `occs` parameter.

All matches of `p` in `e` are considered for occurrences,
but for each match that is included by the `occs` parameter,
metavariables appearing in `p` (or `e`) may become instantiated,
affecting the possibility of subsequent matches.
For matches that are not included in the `occs` parameter, the metavariable context is rolled back
to prevent blocking subsequent matches which require different instantiations.
-/
def kabstract (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← instantiateMVars e
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    -- The state contains the number of matches so far, and the subterms whose traversal found no
    -- match since the last change to the metavariable context. The latter avoids revisiting shared
    -- subterms. It does not depend on `offset`, which is only used to abstract a match, and candidate
    -- subterms have no loose bound variables.
    let rec visit (e : Expr) (offset : Nat) : StateRefT (Nat × Std.HashSet Expr) MetaM Expr := do
      let cacheable := match e with
        | .app .. | .mdata .. | .proj .. | .letE .. | .lam .. | .forallE .. => true
        | _ => false
      if cacheable && (← get).2.contains e then return e
      let i := (← get).1
      let visitChildren : Unit → StateRefT (Nat × Std.HashSet Expr) MetaM Expr := fun _ => do
        match e with
        | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
        | .mdata _ b       => return e.updateMData! (← visit b offset)
        | .proj _ _ b      => return e.updateProj! (← visit b offset)
        | .letE _ t v b _  => return e.updateLetE! (← visit t offset) (← visit v offset) (← visit b (offset+1))
        | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
        | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
        | e                => return e
      let r ← if e.hasLooseBVars then
        visitChildren ()
      else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
        visitChildren ()
      else
        -- We save the metavariable context here,
        -- so that it can be rolled back unless `occs.contains i`.
        let mctx ← getMCtx
        if (← isDefEq e p) then
          if occs.contains i then
            set (i+1, ({} : Std.HashSet Expr))
            return mkBVar offset
          else
            modify fun (_, s) => (i+1, s)
            -- Revert the metavariable context,
            -- so that other matches are still possible.
            setMCtx mctx
            visitChildren ()
        else
          visitChildren ()
      if cacheable && (← get).1 == i then
        modify fun (i, s) => (i, s.insert e)
      return r
    visit e 0 |>.run' (1, {})

end Lean.Meta
