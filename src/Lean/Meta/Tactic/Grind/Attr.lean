/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.EMatchTheorem
public import Lean.Meta.Tactic.Grind.Cases
public import Lean.Meta.Tactic.Grind.ExtAttr

public section

namespace Lean.Meta.Grind

inductive AttrKind where
  | ematch (k : EMatchTheoremKind)
  | cases (eager : Bool)
  | intro
  | infer
  | ext
  | symbol (prio : Nat)

/-- Return theorem kind for `stx` of the form `Attr.grindThmMod` -/
def getAttrKindCore (stx : Syntax) : CoreM AttrKind := do
  match stx with
  | `(Parser.Attr.grindMod|=) => return .ematch (.eqLhs false)
  | `(Parser.Attr.grindMod|= gen) => return .ematch (.eqLhs true)
  | `(Parser.Attr.grindMod|→) => return .ematch .fwd
  | `(Parser.Attr.grindMod|←) => return .ematch (.bwd false)
  | `(Parser.Attr.grindMod|← gen) => return .ematch (.bwd true)
  | `(Parser.Attr.grindMod|=_) => return .ematch (.eqRhs false)
  | `(Parser.Attr.grindMod|=_ gen) => return .ematch (.eqRhs true)
  | `(Parser.Attr.grindMod|_=_) => return .ematch (.eqBoth false)
  | `(Parser.Attr.grindMod|_=_ gen) => return .ematch (.eqBoth true)
  | `(Parser.Attr.grindMod|←=) => return .ematch .eqBwd
  | `(Parser.Attr.grindMod|=>) => return .ematch .leftRight
  | `(Parser.Attr.grindMod|<=) => return .ematch .rightLeft
  | `(Parser.Attr.grindMod|usr) => return .ematch .user
  | `(Parser.Attr.grindMod|gen) => return .ematch (.default true)
  | `(Parser.Attr.grindMod|cases) => return .cases false
  | `(Parser.Attr.grindMod|cases eager) => return .cases true
  | `(Parser.Attr.grindMod|intro) => return .intro
  | `(Parser.Attr.grindMod|ext) => return .ext
  | `(Parser.Attr.grindMod|symbol $prio:prio) =>
    let some prio := prio.raw.isNatLit? | throwErrorAt prio "priority expected"
    return .symbol prio
  | _ => throwError "unexpected `grind` theorem kind: `{stx}`"

/-- Return theorem kind for `stx` of the form `(Attr.grindMod)?` -/
def getAttrKindFromOpt (stx : Syntax) : CoreM AttrKind := do
  if stx[1].isNone then
    return .infer
  else
    getAttrKindCore stx[1][0]

def throwInvalidUsrModifier : CoreM α :=
  throwError "the modifier `usr` is only relevant in parameters for `grind only`"

/--
Auxiliary function for registering `grind`, `grind!`, `grind?`, and `grind!?` attributes.
`grind!` is like `grind` but selects minimal indexable subterms.
The `grind?` and `grind!?` are aliases for `grind` and `grind!` which displays patterns using `logInfo`.
It is just a convenience for users.
-/
private def registerGrindAttr (minIndexable : Bool) (showInfo : Bool) : IO Unit :=
  registerBuiltinAttribute {
    name := match minIndexable, showInfo with
      | false, false => `grind
      | false, true  => `grind?
      | true,  false => `grind!
      | true,  true  => `grind!?
    descr :=
      let header := match minIndexable, showInfo with
        | false, false => "The `[grind]` attribute is used to annotate declarations."
        | false, true  => "The `[grind?]` attribute is identical to the `[grind]` attribute, but displays inferred pattern information."
        | true,  false => "The `[grind!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."
        | true,  true  => "The `[grind!?]` attribute is identical to the `[grind!]` attribute, but displays inferred pattern information."
      header ++ "\
      \
      When applied to an equational theorem, `[grind =]`, `[grind =_]`, or `[grind _=_]`\
      will mark the theorem for use in heuristic instantiations by the `grind` tactic,
      using respectively the left-hand side, the right-hand side, or both sides of the theorem.\
      When applied to a function, `[grind =]` automatically annotates the equational theorems associated with that function.\
      When applied to a theorem `[grind ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem
      (that is, it will use the theorem for backwards reasoning).\
      When applied to a theorem `[grind →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses
      (that is, it will use the theorem for forwards reasoning).\
      \
      The attribute `[grind]` by itself will effectively try `[grind ←]` (if the conclusion is sufficient for instantiation) and then `[grind →]`.\
      \
      The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.\
      For example, if a theorem `@[grind =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,\
      `grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."
    applicationTime := .afterCompilation
    add := fun declName stx attrKind => MetaM.run' do
      match (← getAttrKindFromOpt stx) with
      | .ematch .user => throwInvalidUsrModifier
      | .ematch k => addEMatchAttr declName attrKind k (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
      | .cases eager => addCasesAttr declName eager attrKind
      | .intro =>
        if let some info ← isCasesAttrPredicateCandidate? declName false then
          for ctor in info.ctors do
            addEMatchAttr ctor attrKind (.default false) (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
        else
          throwError "invalid `[grind intro]`, `{.ofConstName declName}` is not an inductive predicate"
      | .ext => addExtAttr declName attrKind
      | .infer =>
        if let some declName ← isCasesAttrCandidate? declName false then
          addCasesAttr declName false attrKind
          if let some info ← isInductivePredicate? declName then
            -- If it is an inductive predicate,
            -- we also add the constructors (intro rules) as E-matching rules
            for ctor in info.ctors do
              addEMatchAttr ctor attrKind (.default false) (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
        else
          addEMatchAttr declName attrKind (.default false) (← getGlobalSymbolPriorities) (minIndexable := minIndexable) (showInfo := showInfo)
      | .symbol prio => addSymbolPriorityAttr declName attrKind prio
    erase := fun declName => MetaM.run' do
      if showInfo then
        throwError "`[grind?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `[grind]` instead"
      if (← isCasesAttrCandidate declName false) then
        eraseCasesAttr declName
      else if (← isExtTheorem declName) then
        eraseExtAttr declName
      else
        eraseEMatchAttr declName
  }

builtin_initialize
  registerGrindAttr (minIndexable := false) (showInfo := true)
  registerGrindAttr (minIndexable := false) (showInfo := false)
  registerGrindAttr (minIndexable := true) (showInfo := true)
  registerGrindAttr (minIndexable := true) (showInfo := false)

end Lean.Meta.Grind
