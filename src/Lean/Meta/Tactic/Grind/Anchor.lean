/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
import Init.Omega
namespace Lean.Meta.Grind

/-!
Anchor (aka stable hash) support for `grind`. We use
anchors to reference terms in the `grind` state.
-/

/--
Hashes names for computing anchors (aka stable hash codes)
-/
def hashName (n : Name) : UInt64 :=
  if n.hasMacroScopes || n.isInaccessibleUserName || n.isImplementationDetail then
    0
  else if isPrivateName n then
    hash (privateToUserName n)
  else if n.isInternal then
    /-
    **Note** We consider hashing the prefix, but it was not good enough.
    For example, an internal name may depend on the name of theorem being defined.
    Moreover, changing a `theorem` to an `example` would break anchors.
    -/
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
    | .const declName _ =>
      /-
      **Note**: we skip matcher declaration names because they may introduce some
      "instability". Recall that `match` auxiliary declarations are reused.
      -/
      if (← isMatcher declName) then pure 0
      else pure <| hashName declName
    | .fvar fvarId =>
      let userName := (← fvarId.getDecl).userName
      pure <| hashName userName
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
            -- **Note**: we ignore instances we computing stable hash codes
            -- TODO: evaluate whether we should ignore regular implicit arguments too.
            unless info.isImplicit do
              r := mix r (← getAnchor arg)
          else
            r := mix r (← getAnchor arg)
        pure r
    | .sort _ | .mvar _ => pure 0
  modify fun s => { s with anchors := s.anchors.insert { expr := e } a }
  return a

/--
Example: `{ numDigits := 4, anchorPrefix := 0x0c88 }.matches 0x0c88ab10ef20206a` returns `true`
-/
public def AnchorRef.matches (anchorRef : AnchorRef) (anchor : UInt64) : Bool :=
  let shift := 64 - anchorRef.numDigits.toUInt64*4
  anchorRef.anchorPrefix == anchor >>> shift

public class HasAnchor (α : Type u) where
  getAnchor : α → UInt64

/--
Returns the number of digits needed to distinguish the anchors in `es`
-/
public def getNumDigitsForAnchors [HasAnchor α] (es : Array α) : Nat :=
  go 4
where
  go (numDigits : Nat) : Nat := Id.run do
    if 4*numDigits  < 64 then
      let shift := 64 - 4*numDigits
      let mut found : Std.HashSet UInt64 := {}
      for e in es do
        let a := HasAnchor.getAnchor e
        let a' := a >>> shift.toUInt64
        if found.contains a' then
          return (← go (numDigits+1))
        else
          found  := found.insert a'
      return numDigits
    else
      return numDigits
  termination_by 64 - 4*numDigits

public structure ExprWithAnchor where
  e      : Expr
  anchor : UInt64

public instance : HasAnchor ExprWithAnchor where
  getAnchor e := e.anchor

public def mkAnchorSyntaxFromPrefix (numDigits : Nat) (anchorPrefix : UInt64) : CoreM (TSyntax ``Parser.Tactic.anchor) := do
  let hexnum := mkNode `hexnum #[mkAtom (anchorPrefixToString numDigits anchorPrefix)]
  `(Parser.Tactic.anchor| #$hexnum)

public def mkAnchorSyntax (numDigits : Nat) (anchor : UInt64) : CoreM (TSyntax ``Parser.Tactic.anchor) := do
  let anchorPrefix := anchor >>> (64 - 4*numDigits.toUInt64)
  mkAnchorSyntaxFromPrefix numDigits anchorPrefix

public def SplitInfo.getAnchor (s : SplitInfo) : GrindM UInt64 := do
  Grind.getAnchor s.getExpr

end Lean.Meta.Grind
