/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.Tactic.Grind.Cases

namespace Lean.Meta.Grind

inductive AttrKind where
  | ematch (k : EMatchTheoremKind)
  | cases (eager : Bool)
  | intro
  | infer

/-- Return theorem kind for `stx` of the form `Attr.grindThmMod` -/
def getAttrKindCore (stx : Syntax) : CoreM AttrKind := do
  match stx with
  | `(Parser.Attr.grindMod| =) => return .ematch .eqLhs
  | `(Parser.Attr.grindMod| →) => return .ematch .fwd
  | `(Parser.Attr.grindMod| ←) => return .ematch .bwd
  | `(Parser.Attr.grindMod| =_) => return .ematch .eqRhs
  | `(Parser.Attr.grindMod| _=_) => return .ematch .eqBoth
  | `(Parser.Attr.grindMod| ←=) => return .ematch .eqBwd
  | `(Parser.Attr.grindMod| usr) => return .ematch .user
  | `(Parser.Attr.grindMod| cases) => return .cases false
  | `(Parser.Attr.grindMod| cases eager) => return .cases true
  | `(Parser.Attr.grindMod| intro) => return .intro
  | _ => throwError "unexpected `grind` theorem kind: `{stx}`"

/-- Return theorem kind for `stx` of the form `(Attr.grindMod)?` -/
def getAttrKindFromOpt (stx : Syntax) : CoreM AttrKind := do
  if stx[1].isNone then
    return .infer
  else
    getAttrKindCore stx[1][0]

def throwInvalidUsrModifier : CoreM α :=
  throwError "the modifier `usr` is only relevant in parameters for `grind only`"

builtin_initialize
  registerBuiltinAttribute {
    name := `grind
    descr :=
      "The `[grind]` attribute is used to annotate declarations.\
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
      | .ematch k => addEMatchAttr declName attrKind k
      | .cases eager => addCasesAttr declName eager attrKind
      | .intro =>
        if let some info ← isCasesAttrPredicateCandidate? declName false then
          for ctor in info.ctors do
            addEMatchAttr ctor attrKind .default
        else
          throwError "invalid `[grind intro]`, `{declName}` is not an inductive predicate"
      | .infer =>
        if let some declName ← isCasesAttrCandidate? declName false then
          addCasesAttr declName false attrKind
          if let some info ← isInductivePredicate? declName then
            -- If it is an inductive predicate,
            -- we also add the contructors (intro rules) as E-matching rules
            for ctor in info.ctors do
              addEMatchAttr ctor attrKind .default
        else
          addEMatchAttr declName attrKind .default
    erase := fun declName => MetaM.run' do
      if (← isCasesAttrCandidate declName false) then
        eraseCasesAttr declName
      else
        eraseEMatchAttr declName
  }

end Lean.Meta.Grind
