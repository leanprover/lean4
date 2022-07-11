/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Parser.Syntax
import Lean.Elab.Util

namespace Lean.Elab.Term
/-
Expand `optional «precedence»` where
 «precedence» := leading_parser " : " >> precedenceParser -/
def expandOptPrecedence (stx : Syntax) : MacroM (Option Nat) :=
  if stx.isNone then
    return none
  else
    return some (← evalPrec stx[0][1])

private def mkParserSeq (ds : Array (Term × Nat)) : TermElabM (Term × Nat) := do
  if ds.size == 0 then
    throwUnsupportedSyntax
  else if ds.size == 1 then
    pure ds[0]!
  else
    let mut (r, stackSum) := ds[0]!
    for (d, stackSz) in ds[1:ds.size] do
      r ← `(ParserDescr.binary `andthen $r $d)
      stackSum := stackSum + stackSz
    return (r, stackSum)

structure ToParserDescrContext where
  catName  : Name
  first    : Bool
  leftRec  : Bool -- true iff left recursion is allowed
  /- See comment at `Parser.ParserCategory`. -/
  behavior : Parser.LeadingIdentBehavior

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT (Option Nat) TermElabM)
abbrev ToParserDescr := ToParserDescrM (Term × Nat)
private def markAsTrailingParser (lhsPrec : Nat) : ToParserDescrM Unit := set (some lhsPrec)

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

def ensureUnaryOutput (x : Term × Nat) : Term :=
  let (stx, stackSz) := x
  if stackSz != 1 then
    Unhygienic.run ``(ParserDescr.unary $(quote `group) $stx)
  else
    stx

@[inline] private def withNestedParser (x : ToParserDescr) : ToParserDescr := do
  withReader (fun ctx => { ctx with leftRec := false, first := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  unless ctx.first && stx.getKind == ``Lean.Parser.Syntax.cat do
    return false
  let cat := stx[0].getId.eraseMacroScopes
  unless cat == ctx.catName do
    return false
  let prec? ← liftMacroM <| expandOptPrecedence stx[1]
  unless ctx.leftRec do
    throwErrorAt stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
  markAsTrailingParser (prec?.getD 0)
  return true

/-- Resolve the given parser name and return a list of candidates.
    Each candidate is a pair `(resolvedParserName, isDescr)`.
    `isDescr == true` if the type of `resolvedParserName` is a `ParserDescr`. -/
def resolveParserName [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] (parserName : Syntax) : m (List (Name × Bool)) := do
  try
    let candidates ← resolveGlobalConstWithInfos parserName
    /- Convert `candidates` in a list of pairs `(c, isDescr)`, where `c` is the parser name,
        and `isDescr` is true iff `c` has type `Lean.ParserDescr` or `Lean.TrailingParser` -/
    let env ← getEnv
    return candidates.filterMap fun c =>
        match env.find? c with
        | none      => none
        | some info =>
          match info.type with
        | Expr.const ``Lean.Parser.TrailingParser _ => (c, false)
        | Expr.const ``Lean.Parser.Parser _         => (c, false)
        | Expr.const ``Lean.ParserDescr _           => (c, true)
        | Expr.const ``Lean.TrailingParserDescr _   => (c, true)
        | _                                         => none
  catch _ => return []

open TSyntax.Compat in
/--
  Given a `stx` of category `syntax`, return a `(newStx, lhsPrec?)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `lhsPrec?.isSome`, and `ParserDescr` otherwise. -/
partial def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Term × Option Nat) := do
  let env ← getEnv
  let behavior := Parser.leadingIdentBehavior env catName
  let ((newStx, _), lhsPrec?) ← (process stx { catName := catName, first := true, leftRec := true, behavior := behavior }).run none
  return (newStx, lhsPrec?)
where
  process (stx : Syntax) : ToParserDescr := withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      processSeq stx
    else if kind == choiceKind then
      process stx[0]
    else if kind == ``Lean.Parser.Syntax.paren then
      process stx[1]
    else if kind == ``Lean.Parser.Syntax.cat then
      processNullaryOrCat stx
    else if kind == ``Lean.Parser.Syntax.unary then
      processAlias stx[0] #[stx[2]]
    else if kind == ``Lean.Parser.Syntax.binary then
      processAlias stx[0] #[stx[2], stx[4]]
    else if kind == ``Lean.Parser.Syntax.sepBy then
      processSepBy stx
    else if kind == ``Lean.Parser.Syntax.sepBy1 then
      processSepBy1 stx
    else if kind == ``Lean.Parser.Syntax.atom then
      processAtom stx
    else if kind == ``Lean.Parser.Syntax.nonReserved then
      processNonReserved stx
    else
      let stxNew? ← liftM (liftMacroM (expandMacro? stx) : TermElabM _)
      match stxNew? with
      | some stxNew => process stxNew
      | none => throwErrorAt stx "unexpected syntax kind of category `syntax`: {kind}"

  /- Sequence (aka NullNode) -/
  processSeq (stx : Syntax) := do
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdx 0
      let args ← args.mapM fun arg => withNestedParser do process arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withReader (fun ctx => { ctx with first := ctx.first && i.val == 0 }) do process arg
      mkParserSeq args

  ensureNoPrec (stx : Syntax) :=
    unless stx[1].isNone do
      throwErrorAt stx[1] "unexpected precedence"

  processParserCategory (stx : Syntax) := do
    let catName := stx[0].getId.eraseMacroScopes
    if (← read).first && catName == (← read).catName then
      throwErrorAt stx "invalid atomic left recursive syntax"
    let prec? ← liftMacroM <| expandOptPrecedence stx[1]
    let prec := prec?.getD 0
    return (← `(ParserDescr.cat $(quote catName) $(quote prec)), 1)

  processAlias (id : Syntax) (args : Array Syntax) := do
    let aliasName := id.getId.eraseMacroScopes
    let info ← Parser.getParserAliasInfo aliasName
    let args ← args.mapM (withNestedParser ∘ process)
    let (args, stackSz) := if let some stackSz := info.stackSz? then
      if !info.autoGroupArgs then
        (args.map (·.1), stackSz)
      else
        (args.map ensureUnaryOutput, stackSz)
    else
      let (args, stackSzs) := args.unzip
      (args, stackSzs.foldl (· + ·) 0)
    let stx ← match args with
      | #[]       => Parser.ensureConstantParserAlias aliasName; ``(ParserDescr.const $(quote aliasName))
      | #[p1]     => Parser.ensureUnaryParserAlias aliasName; ``(ParserDescr.unary $(quote aliasName) $p1)
      | #[p1, p2] => Parser.ensureBinaryParserAlias aliasName; ``(ParserDescr.binary $(quote aliasName) $p1 $p2)
      | _         => unreachable!
    return (stx, stackSz)

  processNullaryOrCat (stx : Syntax) := do
    match (← resolveParserName stx[0]) with
    | [(c, true)]      =>
      ensureNoPrec stx
      -- `syntax _ :=` at least enforces this
      let stackSz := 1
      return (mkIdentFrom stx c, stackSz)
    | [(c, false)]     =>
      ensureNoPrec stx
      -- as usual, we assume that people using `Parser` know what they are doing
      let stackSz := 1
      return (← `(ParserDescr.parser $(quote c)), stackSz)
    | cs@(_ :: _ :: _) => throwError "ambiguous parser declaration {cs.map (·.1)}"
    | [] =>
      let id := stx[0].getId.eraseMacroScopes
      if Parser.isParserCategory (← getEnv) id then
        processParserCategory stx
      else if (← Parser.isParserAlias id) then
        ensureNoPrec stx
        processAlias stx[0] #[]
      else
        throwError "unknown parser declaration/category/alias '{id}'"

  processSepBy (stx : Syntax) := do
    let p ← ensureUnaryOutput <$> withNestedParser do process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else ensureUnaryOutput <$> withNestedParser do process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    return (← `(ParserDescr.sepBy $p $sep $psep $(quote allowTrailingSep)), 1)

  processSepBy1 (stx : Syntax) := do
    let p ← ensureUnaryOutput <$> withNestedParser do process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else ensureUnaryOutput <$> withNestedParser do process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    return (← `(ParserDescr.sepBy1 $p $sep $psep $(quote allowTrailingSep)), 1)

  isValidAtom (s : String) : Bool :=
    !s.isEmpty &&
    s.front != '\'' &&
    s.front != '\"' &&
    !(s.front == '`' && (s.endPos == ⟨1⟩ || isIdFirst (s.get ⟨1⟩) || isIdBeginEscape (s.get ⟨1⟩))) &&
    !s.front.isDigit

  processAtom (stx : Syntax) := do
    match stx[0].isStrLit? with
    | some atom =>
      unless isValidAtom atom do
        throwErrorAt stx "invalid atom"
      /- For syntax categories where initialized with `LeadingIdentBehavior` different from default (e.g., `tactic`), we automatically mark
         the first symbol as nonReserved. -/
      if (← read).behavior != Parser.LeadingIdentBehavior.default && (← read).first then
        return (← `(ParserDescr.nonReservedSymbol $(quote atom) false), 1)
      else
        return (← `(ParserDescr.symbol $(quote atom)), 1)
    | none => throwUnsupportedSyntax

  processNonReserved (stx : Syntax) := do
    match stx[1].isStrLit? with
    | some atom => return (← `(ParserDescr.nonReservedSymbol $(quote atom) false), 1)
    | none      => throwUnsupportedSyntax


end Term

namespace Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
  if let .str _ suffix := catName then
    let quotSymbol := "`(" ++ suffix ++ "|"
    let name := catName ++ `quot
    let cmd ← `(
      @[termParser] def $(mkIdent name) : Lean.ParserDescr :=
        Lean.ParserDescr.node `Lean.Parser.Term.quot $(quote Lean.Parser.maxPrec)
          (Lean.ParserDescr.node $(quote name) $(quote Lean.Parser.maxPrec)
            (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol $(quote quotSymbol))
              (Lean.ParserDescr.binary `andthen
                (Lean.ParserDescr.cat $(quote catName) 0)
                (Lean.ParserDescr.symbol ")")))))
    elabCommand cmd

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab := fun stx => do
  let catName  := stx[1].getId
  let catBehavior :=
    if stx[2].isNone then
      Parser.LeadingIdentBehavior.default
    else if stx[2][3].getKind == ``Parser.Command.catBehaviorBoth then
      Parser.LeadingIdentBehavior.both
    else
      Parser.LeadingIdentBehavior.symbol
  let attrName := catName.appendAfter "Parser"
  let env ← getEnv
  let env ← Parser.registerParserCategory env attrName catName catBehavior
  setEnv env
  declareSyntaxCatQuotParser catName

/--
  Auxiliary function for creating declaration names from parser descriptions.
  Example:
  Given
  ```
  syntax term "+" term : term
  syntax "[" sepBy(term, ", ") "]"  : term
  ```
  It generates the names `term_+_` and `term[_,]`
-/
partial def mkNameFromParserSyntax (catName : Name) (stx : Syntax) : MacroM Name := do
  mkUnusedBaseName <| Name.mkSimple <| appendCatName <| visit stx ""
where
  visit (stx : Syntax) (acc : String) : String :=
    match stx.isStrLit? with
    | some val => acc ++ (val.trim.map fun c => if c.isWhitespace then '_' else c).capitalize
    | none =>
      match stx with
      | Syntax.node _ k args =>
        if k == ``Lean.Parser.Syntax.cat then
          acc ++ "_"
        else
          args.foldl (init := acc) fun acc arg => visit arg acc
      | Syntax.ident ..    => acc
      | Syntax.atom ..     => acc
      | Syntax.missing     => acc

  appendCatName (str : String) :=
    match catName with
    | .str _ s => s ++ str
    | _ => str

/- We assume a new syntax can be treated as an atom when it starts and ends with a token.
   Here are examples of atom-like syntax.
   ```
   syntax "(" term ")" : term
   syntax "[" (sepBy term ",") "]" : term
   syntax "foo" : term
   ```
 -/
private partial def isAtomLikeSyntax (stx : Syntax) : Bool :=
  let kind := stx.getKind
  if kind == nullKind then
    isAtomLikeSyntax stx[0] && isAtomLikeSyntax stx[stx.getNumArgs - 1]
  else if kind == choiceKind then
    isAtomLikeSyntax stx[0] -- see toParserDescr
  else if kind == ``Lean.Parser.Syntax.paren then
    isAtomLikeSyntax stx[1]
  else
    kind == ``Lean.Parser.Syntax.atom

def resolveSyntaxKind (k : Name) : CommandElabM Name := do
  checkSyntaxNodeKindAtNamespaces k (← getCurrNamespace)
  <|>
  throwError "invalid syntax node kind '{k}'"

@[builtinCommandElab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let `($[$doc?:docComment]? $attrKind:attrKind syntax $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $[$ps:stx]* : $catStx) ← pure stx
    | throwUnsupportedSyntax
  let cat := catStx.getId.eraseMacroScopes
  unless (Parser.isParserCategory (← getEnv) cat) do
    throwErrorAt catStx "unknown category '{cat}'"
  let syntaxParser := mkNullNode ps
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec ← match prec? with
    | some prec => liftMacroM <| evalPrec prec
    | none      => pure precDefault
  let name ← match name? with
    | some name => pure name.getId
    | none => liftMacroM <| mkNameFromParserSyntax cat syntaxParser
  let prio ← liftMacroM <| evalOptPrio prio?
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser")
  let (val, lhsPrec?) ← runTermElabM none fun _ => Term.toParserDescr syntaxParser cat
  let declName := mkIdentFrom stx name
  let d ← if let some lhsPrec := lhsPrec? then
    `($[$doc?:docComment]? @[$attrKind:attrKind $catParserId:ident $(quote prio):num] def $declName:ident : Lean.TrailingParserDescr :=
        ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $(quote lhsPrec) $val)
  else
    `($[$doc?:docComment]? @[$attrKind:attrKind $catParserId:ident $(quote prio):num] def $declName:ident : Lean.ParserDescr :=
        ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d <| elabCommand d

@[builtinCommandElab «syntaxAbbrev»] def elabSyntaxAbbrev : CommandElab := fun stx => do
  let `($[$doc?:docComment]? syntax $declName:ident := $[$ps:stx]*) ← pure stx | throwUnsupportedSyntax
  -- TODO: nonatomic names
  let (val, _) ← runTermElabM none fun _ => Term.toParserDescr (mkNullNode ps) Name.anonymous
  let stxNodeKind := (← getCurrNamespace) ++ declName.getId
  let stx' ← `($[$doc?:docComment]? def $declName:ident : Lean.ParserDescr := ParserDescr.nodeWithAntiquot $(quote (toString declName.getId)) $(quote stxNodeKind) $val)
  withMacroExpansion stx stx' <| elabCommand stx'

def checkRuleKind (given expected : SyntaxNodeKind) : Bool :=
  given == expected || given == expected ++ `antiquot

def inferMacroRulesAltKind : TSyntax ``matchAlt → CommandElabM SyntaxNodeKind
  | `(matchAltExpr| | $pat:term => $_) => do
    if !pat.raw.isQuot then
      throwUnsupportedSyntax
    let quoted := getQuotContent pat
    pure quoted.getKind
  | _ => throwUnsupportedSyntax

/--
Infer syntax kind `k` from first pattern, put alternatives of same kind into new `macro/elab_rules (kind := k)` via `mkCmd (some k)`,
leave remaining alternatives (via `mkCmd none`) to be recursively expanded. -/
def expandNoKindMacroRulesAux (alts : Array (TSyntax ``matchAlt)) (cmdName : String) (mkCmd : Option Name → Array (TSyntax ``matchAlt) → CommandElabM Command) : CommandElabM Command := do
  let mut k ← inferMacroRulesAltKind alts[0]!
  if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
  if k == choiceKind then
    throwErrorAt alts[0]!
      "invalid {cmdName} alternative, multiple interpretations for pattern (solution: specify node kind using `{cmdName} (kind := ...) ...`)"
  else
    let altsK    ← alts.filterM fun alt => return checkRuleKind (← inferMacroRulesAltKind alt) k
    let altsNotK ← alts.filterM fun alt => return !checkRuleKind (← inferMacroRulesAltKind alt) k
    if altsNotK.isEmpty then
      mkCmd k altsK
    else
      `($(← mkCmd k altsK):command $(← mkCmd none altsNotK))

def strLitToPattern (stx: Syntax) : MacroM Syntax :=
  match stx.isStrLit? with
  | some str => return mkAtomFrom stx str
  | none     => Macro.throwUnsupported

builtin_initialize
  registerTraceClass `Elab.syntax

end Lean.Elab.Command
