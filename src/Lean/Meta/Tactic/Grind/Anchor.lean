/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
namespace Lean.Meta.Grind

/-!
Anchor (aka stable hash) support for `grind`. We use
anchors to reference terms in the `grind` state.
-/

/--
Hashes names for computing anchors (aka stable hash codes)
-/
def hashName (n : Name) : UInt64 :=
  if n.isInaccessibleUserName || n.isImplementationDetail then
    0
  else
    hash n

-- `mixHash` variant where `0` is treated as don't care
def mix (a b : UInt64) : UInt64 :=
  if a == 0 then b
  else if b == 0 then a
  else mixHash a b

public partial def getAnchor (e : Expr) : GrindM UInt64 := do
  if let some a := (← get).anchors.find? { expr := e } then
    return a
  let a ← match e with
    | .const declName _ => pure <| hash declName
    | .fvar fvarId => pure <| hashName (← fvarId.getDecl).userName
    | .mdata _ b => getAnchor b
    | .letE n v t b _ =>
      pure <| mix (hashName n) <| mix (← getAnchor t) <| mix (← getAnchor v) (← getAnchor b)
    | .lam n d b _ | .forallE n d b _ =>
      pure <| mix (hashName n) <| mix (← getAnchor d) (← getAnchor b)
    | .proj _ i s => pure <| mix (hash i) (← getAnchor s)
    | .bvar idx => pure <| hash idx
    | .lit v => pure <| hash v
    | .app .. => e.withApp fun f args => do
      if isMarkedSubsingletonConst f && args.size == 2 then
        -- **Note**: we only visit the type of marked subsingleton terms.
        getAnchor args[0]!
      else
        let pinfos ← if f.hasLooseBVars then
          pure #[]
        else
          pure <| (← getFunInfo f).paramInfo
        let mut r ← getAnchor f
        for h : i in *...args.size do
          let arg := args[i]
          if h : i < pinfos.size then
            let info := pinfos[i]
            -- **Note**: we ignore implicit instances we computing stable hash codes
            -- TODO: evaluate whether we should ignore regular implicit arguments too.
            unless info.isInstImplicit do
              r := mix r (← getAnchor arg)
          else
            r := mix r (← getAnchor arg)
        pure r
    | .sort _ | .mvar _ => pure 0
  modify fun s => { s with anchors := s.anchors.insert { expr := e } a }
  return a

end Lean.Meta.Grind
