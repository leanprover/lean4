/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.FunIndInfo

/-!
Support for collecting function calls that could be used for `fun_induction` or `fun_cases`.
Used by `fun_induction foo`, and the `Calls` structure is also used by `try?`.
-/

namespace Lean.Meta.FunInd

structure Call where
  /- The full function call -/
  expr : Expr
  /- Used to avoid adding calls that differ only in dropped arguments -/
  relevantArgs : Expr
  deriving Hashable, BEq

structure SeenCalls where
  /-- the full calls -/
  calls : Array Expr
  /-- only function name and relevant arguments -/
  seen : Std.HashSet (Name × Array Expr)

instance : EmptyCollection SeenCalls where
  emptyCollection := ⟨#[], {}⟩

def SeenCalls.isEmpty  (sc : SeenCalls) : Bool :=
  sc.calls.isEmpty

def SeenCalls.push (e : Expr) (declName : Name) (args : Array Expr) (calls : SeenCalls) :
    MetaM SeenCalls := do
  let some funIndInfo ← getFunIndInfo? (cases := false) declName | return calls
  if funIndInfo.params.size != args.size then return calls
  let mut keys := #[]
  for arg in args, kind in funIndInfo.params do
    if kind matches .target then
      if !arg.isFVar then return calls
    unless kind matches .dropped do
      keys := keys.push arg
  let key := (declName, keys)
  if calls.seen.contains key then return calls
  return { calls := calls.calls.push e, seen := calls.seen.insert key }

/--
Which functions have exactly one candidate application. Used by `try?` to determine whether
we can use `fun_induction foo` or need `fun_induction foo x y z`.
-/
def SeenCalls.uniques (calls : SeenCalls) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut seenTwice : NameSet := {}
  for (n, _) in calls.seen do
    unless seenTwice.contains n do
      if seen.contains n then
        seenTwice := seenTwice.insert n
      else
        seen := seen.insert n
  return seen.filter (! seenTwice.contains ·)

namespace Collector

abbrev M := ReaderT Name <| StateRefT SeenCalls MetaM

def saveFunInd (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  set (← (← get).push e declName args)

def visitApp (e : Expr) (declName : Name) (args : Array Expr) : M Unit := do
  saveFunInd e declName args

unsafe abbrev Cache := PtrSet Expr

unsafe def visit (e : Expr) : StateRefT Cache M Unit := do
  unless (← get).contains e do
    modify fun s => s.insert e
    match e with
      | .const _ _        => pure ()
      | .forallE _ d b _  => visit d; visit b
      | .lam _ d b _      => visit d; visit b
      | .mdata _ b        => visit b
      | .letE _ t v b _   => visit t; visit v; visit b
      | .app ..           => e.withApp fun f args => do
        if let .const declName _ := f then
          if declName = (← read) then
            unless e.hasLooseBVars do -- TODO: We can allow them in `.dropped` arguments
              visitApp e declName args
        else
          visit f
        args.forM visit
      | .proj _ _ b       => visit b
      | _                 => return ()

unsafe def main (needle : Name) (mvarId : MVarId) : MetaM (Array Expr) := mvarId.withContext do
  let (_, s) ← go |>.run mkPtrSet |>.run needle |>.run {}
  return s.calls
where
  go : StateRefT Cache M Unit := do
    for localDecl in (← getLCtx) do
      unless localDecl.isAuxDecl do
        if let some val := localDecl.value? then
          visit val
        else
          visit localDecl.type
    visit (← mvarId.getType)

end Collector

def collect (needle : Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  unsafe Collector.main needle mvarId

end Lean.Meta.FunInd
