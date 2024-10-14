import Lean

open Lean Meta

namespace Lean.Meta.MVarCycles

/-- How the expression relates to the mvar (type, expression, delayed) -/
inductive ToA where | T | A | D

abbrev Path := Array (MVarId × ToA × Expr)

-- I failed to prevent {Expr.mvar mvarId} from instantiating the mvar
-- even with `withOptions (pp.instantiateMVars.set · false) do`
def ppMVar (mvarId : MVarId) : MetaM MessageData := do
  let mvarDecl ← mvarId.getDecl
  let n :=
    match mvarDecl.userName with
    | .anonymous => mvarId.name.replacePrefix `_uniq `m
    | n => n
  return m!"?{mkIdent n}"

def raiseCyclicMVarError (path : Path) : MetaM Unit := do
  let mut msg := m!"Found cycle in the mvar context:"
  for (mvarId, toa, e) in path do
    match toa with
    | .T => msg := msg ++ m!"\n{← ppMVar mvarId} :: {e}"
    | .A => msg := msg ++ m!"\n{← ppMVar mvarId} := {e}"
    | .D => msg := msg ++ m!"\n{← ppMVar mvarId} := {e} (delayed assignment)"
  throwError msg

/-!
Checks the current MVar assignemnts and types for cycles and if it finds one, throws an exception
with a pretty representation thereof. Level MVars are ignored for now.
-/

partial def checkMVarsCycles : MetaM Unit := StateT.run' (s := {}) do
  let mctxt ← getMCtx
  for (mvarid, _) in mctxt.decls do
    go #[] mvarid
where
  go (path : Path) (mvarId : MVarId) : StateT (Std.HashSet MVarId) MetaM Unit := do
    -- already handled this mvar?
    if (← get).contains mvarId then return

    -- did we find a cycle?
    if let .some i := path.findIdx? (·.1 == mvarId) then
      raiseCyclicMVarError path[i:]

    -- traverse the type
    let t :=  (← mvarId.getDecl).type
    goE (path.push (mvarId, .T, t)) t
    -- traverse the expression assignemnt
    if let .some e ← getExprMVarAssignment? mvarId then
      goE (path.push (mvarId, .A, e)) e
    -- traverse the delayed assignemnt
    if let .some da ← getDelayedMVarAssignment? mvarId then
      go (path.push (mvarId, .A, .mvar da.mvarIdPending)) da.mvarIdPending

    -- all good? Remember as such
    modify (·.insert mvarId)

  goE (path : Path) (e : Expr) : StateT (Std.HashSet MVarId) MetaM Unit := do
    if !e.hasMVar then return
    match e with
    | (.lit _)           => return
    | (.bvar _)          => return
    | (.fvar _)          => return
    | (.sort _)          => return
    | (.const _ _)      => return
    | (.proj _ _ s)      => goE path s
    | (.app f a)         => goE path f; goE path a
    | (.mdata _ b)       => goE path b
    | (.lam _ d b _)     => goE path d; goE path b
    | (.forallE _ d b _) => goE path d; goE path b
    | (.letE _ t v b _)  => goE path t; goE path v; goE path b
    | (.mvar mvarId)     => go path mvarId

end Lean.Meta.MVarCycles
