/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Attr
import Lean.Parser.Level

namespace Lean
namespace Parser

namespace Command
def commentBody : Parser :=
{ fn := rawFn (finishCommentBlock 1) (trailingWs := true) }

@[combinatorParenthesizer Lean.Parser.Command.commentBody] def commentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinatorFormatter Lean.Parser.Command.commentBody] def commentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def docComment       := leading_parser ppDedent $ "/--" >> ppSpace >> commentBody >> ppLine
end Command

builtin_initialize
  registerBuiltinParserAttribute `builtinTacticParser `tactic LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `tacticParser `tactic

@[inline] def tacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `tactic rbp

@[inline] def convParser (rbp : Nat := 0) : Parser :=
  categoryParser `conv rbp

namespace Tactic

def tacticSeq1Indented : Parser :=
  leading_parser many1Indent (group (ppLine >> tacticParser >> optional ";"))
def tacticSeqBracketed : Parser :=
  leading_parser "{" >> many (group (ppLine >> tacticParser >> optional ";")) >> ppDedent (ppLine >> "}")
def tacticSeq :=
  leading_parser tacticSeqBracketed <|> tacticSeq1Indented

/-- Raw sequence for quotation and grouping -/
def seq1 :=
  node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" (allowTrailingSep := true)

end Tactic

def darrow : Parser := " => "
def semicolonOrLinebreak := ";" <|> checkLinebreakBefore >> pushNone

namespace Term

/-! # Built-in parsers -/

@[builtinTermParser] def byTactic := leading_parser:leadPrec ppAllowUngrouped >> "by " >> Tactic.tacticSeq

/--
  This is the same as `byTactic`, but it uses a different syntax kind. This is
  used by `show` and `suffices` instead of `byTactic` because these syntaxes don't
  support arbitrary terms where `byTactic` is accepted. Mathport uses this to e.g.
  safely find-replace `by exact $e` by `$e` in any context without causing
  incorrect syntax when the full expression is `show $T by exact $e`. -/
def byTactic' := leading_parser "by " >> Tactic.tacticSeq

-- TODO: rename to e.g. `afterSemicolonOrLinebreak`
def optSemicolon (p : Parser) : Parser := ppDedent $ semicolonOrLinebreak >> ppLine >> p

-- `checkPrec` necessary for the pretty printer
@[builtinTermParser] def ident := checkPrec maxPrec >> Parser.ident
@[builtinTermParser] def num : Parser := checkPrec maxPrec >> numLit
@[builtinTermParser] def scientific : Parser := checkPrec maxPrec >> scientificLit
@[builtinTermParser] def str : Parser := checkPrec maxPrec >> strLit
@[builtinTermParser] def char : Parser := checkPrec maxPrec >> charLit
@[builtinTermParser] def type := leading_parser "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def sort := leading_parser "Sort" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def prop := leading_parser "Prop"
@[builtinTermParser] def hole := leading_parser "_"
@[builtinTermParser] def syntheticHole := leading_parser "?" >> (ident <|> hole)
@[builtinTermParser] def «sorry» := leading_parser "sorry"
@[builtinTermParser] def cdot   := leading_parser symbol "·" <|> "."
def typeAscription := leading_parser " : " >> termParser
def tupleTail      := leading_parser ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := leading_parser "(" >> (withoutPosition (withoutForbidden (optional (ppDedentIfGrouped termParser >> parenSpecial)))) >> ")"
@[builtinTermParser] def anonymousCtor := leading_parser "⟨" >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (atomic (ident >> " : "))
def fromTerm   := leading_parser "from " >> termParser
def showRhs := fromTerm <|> byTactic'
def sufficesDecl := leading_parser optIdent >> termParser >> ppSpace >> showRhs
@[builtinTermParser] def «suffices» := leading_parser:leadPrec withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtinTermParser] def «show»     := leading_parser:leadPrec "show " >> termParser >> ppSpace >> showRhs
def structInstArrayRef := leading_parser "[" >> termParser >>"]"
def structInstLVal   := leading_parser (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := ppGroup $ leading_parser structInstLVal >> " := " >> termParser
def structInstFieldAbbrev := leading_parser atomic (ident >> notFollowedBy ("." <|> ":=" <|> symbol "[") "invalid field abbreviation") -- `x` is an abbreviation for `x := x`
def optEllipsis      := leading_parser optional ".."
@[builtinTermParser] def structInst := leading_parser "{" >> ppHardSpace >> optional (atomic (sepBy1 termParser ", " >> " with "))
  >> sepByIndent (structInstFieldAbbrev <|> structInstField) ", " (allowTrailingSep := true)
  >> optEllipsis
  >> optional (" : " >> termParser) >> " }"
def typeSpec := leading_parser " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def explicit := leading_parser "@" >> termParser maxPrec
@[builtinTermParser] def inaccessible := leading_parser ".(" >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then node nullKind (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := leading_parser atomic (symbol " := " >> " by ") >> Tactic.tacticSeq
def binderDefault := leading_parser " := " >> termParser
def explicitBinder (requireType := false) := ppGroup $ leading_parser "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := ppGroup $ leading_parser "{" >> many1 binderIdent >> binderType requireType >> "}"
def strictImplicitLeftBracket := atomic (group (symbol "{" >> "{")) <|> "⦃"
def strictImplicitRightBracket := atomic (group (symbol "}" >> "}")) <|> "⦄"
def strictImplicitBinder (requireType := false) := ppGroup $ leading_parser strictImplicitLeftBracket >> many1 binderIdent >> binderType requireType >> strictImplicitRightBracket
def instBinder := ppGroup $ leading_parser "[" >> optIdent >> termParser >> "]"
def bracketedBinder (requireType := false) := withAntiquot (mkAntiquot "bracketedBinder" `Lean.Parser.Term.bracketedBinder (isPseudoKind := true)) <|
  explicitBinder requireType <|> strictImplicitBinder requireType <|> implicitBinder requireType <|> instBinder

/--
It is feasible to support dependent arrows such as `{α} → α → α` without sacrificing the quality of the error messages for the longer case.
`{α} → α → α` would be short for `{α : Type} → α → α`
Here is the encoding:
```
def implicitShortBinder := node `Lean.Parser.Term.implicitBinder $ "{" >> many1 binderIdent >> pushNone >> "}"
def depArrowShortPrefix := try (implicitShortBinder >> unicodeSymbol " → " " -> ")
def depArrowLongPrefix  := bracketedBinder true >> unicodeSymbol " → " " -> "
def depArrowPrefix      := depArrowShortPrefix <|> depArrowLongPrefix
@[builtinTermParser] def depArrow := leading_parser depArrowPrefix >> termParser
```
Note that no changes in the elaborator are needed.
We decided to not use it because terms such as `{α} → α → α` may look too cryptic.
Note that we did not add a `explicitShortBinder` parser since `(α) → α → α` is really cryptic as a short for `(α : Type) → α → α`.
-/
@[builtinTermParser] def depArrow := leading_parser:25 bracketedBinder true >> unicodeSymbol " → " " -> " >> termParser

@[builtinTermParser]
def «forall» := leading_parser:leadPrec unicodeSymbol "∀" "forall" >> many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >> optType >> ", " >> termParser

def matchAlt (rhsParser : Parser := termParser) : Parser :=
  leading_parser (withAnonymousAntiquot := false)
    "| " >> ppIndent (sepBy1 (sepBy1 termParser ", ") "|" >> darrow >> checkColGe "alternative right-hand-side to start in a column greater than or equal to the corresponding '|'" >> rhsParser)
/--
  Useful for syntax quotations. Note that generic patterns such as `` `(matchAltExpr| | ... => $rhs) `` should also
  work with other `rhsParser`s (of arity 1). -/
def matchAltExpr := matchAlt

instance : Coe (TSyntax ``matchAltExpr) (TSyntax ``matchAlt) where
  coe stx := ⟨stx.raw⟩

def matchAlts (rhsParser : Parser := termParser) : Parser :=
  leading_parser withPosition $ many1Indent (ppLine >> matchAlt rhsParser)

def matchDiscr := leading_parser optional (atomic (ident >> " : ")) >> termParser

def trueVal  := leading_parser nonReservedSymbol "true"
def falseVal := leading_parser nonReservedSymbol "false"
def generalizingParam := leading_parser atomic ("(" >> nonReservedSymbol "generalizing") >> " := " >> (trueVal <|> falseVal)  >> ")" >> ppSpace

def motive := leading_parser atomic ("(" >> nonReservedSymbol "motive" >> " := ") >> termParser >> ")" >> ppSpace

@[builtinTermParser] def «match» := leading_parser:leadPrec "match " >> optional generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >> " with " >> ppDedent matchAlts
@[builtinTermParser] def «nomatch» := leading_parser:leadPrec "nomatch " >> termParser

def funImplicitBinder := withAntiquot (mkAntiquot "implicitBinder" ``implicitBinder) <| atomic (lookahead ("{" >> many1 binderIdent >> (symbol " : " <|> "}"))) >> implicitBinder
def funStrictImplicitBinder := atomic (lookahead (strictImplicitLeftBracket >> many1 binderIdent >> (symbol " : " <|> strictImplicitRightBracket))) >> strictImplicitBinder
def funBinder : Parser := withAntiquot (mkAntiquot "funBinder" `Lean.Parser.Term.funBinder (isPseudoKind := true)) (funStrictImplicitBinder <|> funImplicitBinder <|> instBinder <|> termParser maxPrec)
-- NOTE: we disable anonymous antiquotations to ensure that `fun $b => ...` remains a `term` antiquotation
def basicFun : Parser := leading_parser (withAnonymousAntiquot := false) ppGroup (many1 (ppSpace >> funBinder) >> optType >> " =>") >> ppSpace >> termParser
@[builtinTermParser] def «fun» := leading_parser:maxPrec ppAllowUngrouped >> unicodeSymbol "λ" "fun" >> (basicFun <|> matchAlts)

def optExprPrecedence := optional (atomic ":" >> termParser maxPrec)
def withAnonymousAntiquot := leading_parser atomic ("(" >> nonReservedSymbol "withAnonymousAntiquot" >> " := ") >> (trueVal <|> falseVal) >> ")" >> ppSpace
@[builtinTermParser] def «leading_parser»  := leading_parser:leadPrec "leading_parser " >> optExprPrecedence >> optional withAnonymousAntiquot >> termParser
@[builtinTermParser] def «trailing_parser» := leading_parser:leadPrec "trailing_parser " >> optExprPrecedence >> optExprPrecedence >> termParser

@[builtinTermParser] def borrowed   := leading_parser "@& " >> termParser leadPrec
@[builtinTermParser] def quotedName := leading_parser nameLit
-- use `rawCh` because ``"`" >> ident`` overlaps with `nameLit`, with the latter being preferred by the tokenizer
-- note that we cannot use ```"``"``` as a new token either because it would break `precheckedQuot`
@[builtinTermParser] def doubleQuotedName := leading_parser "`" >> checkNoWsBefore >> rawCh '`' (trailingWs := false) >> ident

def letIdBinder := withAntiquot (mkAntiquot "letIdBinder" `Lean.Parser.Term.letIdBinder (isPseudoKind := true)) (binderIdent <|> bracketedBinder)
/-- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> notFollowedBy (checkNoWsBefore "" >> "[") "space is required before instance '[...]' binders to distinguish them from array updates `let x[i] := e; ...`" >> many (ppSpace >> letIdBinder) >> optType
def letIdDecl   := leading_parser (withAnonymousAntiquot := false) atomic (letIdLhs >> " := ") >> termParser
def letPatDecl  := leading_parser (withAnonymousAntiquot := false) atomic (termParser >> pushNone >> optType >> " := ") >> termParser
/--
  Remark: the following `(" := " <|> matchAlts)` is a hack we use to produce a better error message at `letDecl`.
  Consider this following example
  ```
  def myFun (n : Nat) : IO Nat :=
    let q ← (10 : Nat)
    n + q
  ```
  Without the hack, we get the error `expected '|'` at `←`. Reason: at `letDecl`, we use the parser `(letIdDecl <|> letPatDecl <|> letEqnsDecl)`,
  `letIdDecl` and `letEqnsDecl` have the same prefix `letIdLhs`, but `letIdDecl` uses `atomic`.
  Note that the hack relies on the fact that the parser `":="` never succeeds at `(" := " <|> matchAlts)`. It is there just to make sure we produce the error `expected ':=' or '|'`
-/
def letEqnsDecl := leading_parser (withAnonymousAntiquot := false) letIdLhs >> (" := " <|> matchAlts)
-- Remark: we disable anonymous antiquotations here to make sure anonymous antiquotations (e.g., `$x`) are not `letDecl`
def letDecl     := leading_parser (withAnonymousAntiquot := false) notFollowedBy (nonReservedSymbol "rec") "rec" >> (letIdDecl <|> letPatDecl <|> letEqnsDecl)
/--
`let` is used to declare a local definition. Example:
```
let x := 1
let y := x + 1
x + y
```
Since functions are first class citizens in Lean, you can use `let` to declare local functions too.
```
let double := fun x => 2*x
double (double 3)
```
For recursive definitions, you should use `let rec`.
You can also perform pattern matching using `let`. For example, assume `p` has type `Nat × Nat`, then you can write
```
let (x, y) := p
x + y
```
-/
@[builtinTermParser] def «let» := leading_parser:leadPrec  withPosition ("let " >> letDecl) >> optSemicolon termParser
/--
`let_fun x := v; b` is syntax sugar for `(fun x => b) v`. It is very similar to `let x := v; b`, but they are not equivalent.
In `let_fun`, the value `v` has been abstracted away and cannot be accessed in `b`.
-/
@[builtinTermParser] def «let_fun»     := leading_parser:leadPrec withPosition ((symbol "let_fun " <|> "let_λ") >> letDecl) >> optSemicolon termParser
/--
`let_delayed x := v; b` is similar to `let x := v; b`, but `b` is elaborated before `v`.
-/
@[builtinTermParser] def «let_delayed» := leading_parser:leadPrec withPosition ("let_delayed " >> letDecl) >> optSemicolon termParser
/--
`let`-declaration that is only included in the elaborated term if variable is still there.
It is often used when building macros.
-/
@[builtinTermParser] def «let_tmp» := leading_parser:leadPrec withPosition ("let_tmp " >> letDecl) >> optSemicolon termParser

instance : Coe (TSyntax ``letIdBinder) (TSyntax ``funBinder) where
  coe stx := ⟨stx⟩

/-- like `let_fun` but with optional name -/
def haveIdLhs    := optional (ident >> many (ppSpace >> letIdBinder)) >> optType
def haveIdDecl   := leading_parser (withAnonymousAntiquot := false) atomic (haveIdLhs >> " := ") >> termParser
def haveEqnsDecl := leading_parser (withAnonymousAntiquot := false) haveIdLhs >> matchAlts
def haveDecl     := leading_parser (withAnonymousAntiquot := false) haveIdDecl <|> letPatDecl <|> haveEqnsDecl
@[builtinTermParser] def «have» := leading_parser:leadPrec withPosition ("have " >> haveDecl) >> optSemicolon termParser

def «scoped» := leading_parser "scoped "
def «local»  := leading_parser "local "
def attrKind := leading_parser optional («scoped» <|> «local»)
def attrInstance     := ppGroup $ leading_parser attrKind >> attrParser

def attributes       := leading_parser "@[" >> sepBy1 attrInstance ", " >> "]"
def letRecDecl       := leading_parser optional Command.docComment >> optional «attributes» >> letDecl
def letRecDecls      := leading_parser sepBy1 letRecDecl ", "
@[builtinTermParser]
def «letrec» := leading_parser:leadPrec withPosition (group ("let " >> nonReservedSymbol "rec ") >> letRecDecls) >> optSemicolon termParser

@[runBuiltinParserAttributeHooks]
def whereDecls := leading_parser " where" >> sepBy1Indent (ppGroup letRecDecl) "; " (allowTrailingSep := true)

@[runBuiltinParserAttributeHooks]
def matchAltsWhereDecls := leading_parser matchAlts >> optional whereDecls

@[builtinTermParser] def noindex := leading_parser "no_index " >> termParser maxPrec

@[builtinTermParser] def binrel := leading_parser "binrel% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec
/-- Similar to `binrel`, but coerse `Prop` arguments into `Bool`. -/
@[builtinTermParser] def binrel_no_prop := leading_parser "binrel_no_prop% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec
@[builtinTermParser] def binop  := leading_parser "binop% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec
@[builtinTermParser] def binop_lazy  := leading_parser "binop_lazy% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec

@[builtinTermParser] def forInMacro := leading_parser "for_in% " >> termParser maxPrec >> termParser maxPrec >> termParser maxPrec
@[builtinTermParser] def forInMacro' := leading_parser "for_in'% " >> termParser maxPrec >> termParser maxPrec >> termParser maxPrec

@[builtinTermParser] def declName           := leading_parser "decl_name%"
@[builtinTermParser] def withDeclName       := leading_parser "with_decl_name% " >> optional "?" >> ident >> termParser
@[builtinTermParser] def typeOf             := leading_parser "type_of% " >> termParser maxPrec
@[builtinTermParser] def ensureTypeOf       := leading_parser "ensure_type_of% " >> termParser maxPrec >> strLit >> termParser
@[builtinTermParser] def ensureExpectedType := leading_parser "ensure_expected_type% " >> strLit >> termParser maxPrec
@[builtinTermParser] def noImplicitLambda   := leading_parser "no_implicit_lambda% " >> termParser maxPrec

@[builtinTermParser] def letMVar                := leading_parser "let_mvar% " >> "?" >> ident >> " := " >> termParser >> "; " >> termParser
@[builtinTermParser] def waitIfTypeMVar         := leading_parser "wait_if_type_mvar% " >> "?" >> ident >> "; " >> termParser
@[builtinTermParser] def waitIfTypeContainsMVar := leading_parser "wait_if_type_contains_mvar% " >> "?" >> ident >> "; " >> termParser
@[builtinTermParser] def waitIfContainsMVar     := leading_parser "wait_if_contains_mvar% " >> "?" >> ident >> "; " >> termParser

@[builtinTermParser] def defaultOrOfNonempty   := leading_parser "default_or_ofNonempty% " >> optional "unsafe"

/--
Helper parser for marking `match`-alternatives that should not trigger errors if unused.
We use them to implement `macro_rules` and `elab_rules`
-/
@[builtinTermParser] def noErrorIfUnused := leading_parser "no_error_if_unused%" >> termParser

def namedArgument  := leading_parser (withAnonymousAntiquot := false) atomic ("(" >> ident >> " := ") >> termParser >> ")"
def ellipsis       := leading_parser (withAnonymousAntiquot := false) ".."
def argument       :=
  checkWsBefore "expected space" >>
  checkColGt "expected to be indented" >>
  (namedArgument <|> ellipsis <|> termParser argPrec)
-- `app` precedence is `lead` (cannot be used as argument)
-- `lhs` precedence is `max` (i.e. does not accept `arg` precedence)
-- argument precedence is `arg` (i.e. does not accept `lead` precedence)
@[builtinTermParser] def app      := trailing_parser:leadPrec:maxPrec many1 argument

@[builtinTermParser] def proj     := trailing_parser checkNoWsBefore >> "." >> checkNoWsBefore >> (fieldIdx <|> rawIdent)
@[builtinTermParser] def completion := trailing_parser checkNoWsBefore >> "."
@[builtinTermParser] def arrow    := trailing_parser checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser 25

def isIdent (stx : Syntax) : Bool :=
  -- antiquotations should also be allowed where an identifier is expected
  stx.isAntiquot || stx.isIdent

@[builtinTermParser] def explicitUniv : TrailingParser := trailing_parser checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '.{'" >> ".{" >> sepBy1 levelParser ", " >> "}"
@[builtinTermParser] def namedPattern : TrailingParser := trailing_parser checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '@'" >> "@" >> optional (atomic (ident >> ":")) >> termParser maxPrec

@[builtinTermParser] def pipeProj   := trailing_parser:minPrec " |>." >> checkNoWsBefore >> (fieldIdx <|> rawIdent) >> many argument
@[builtinTermParser] def pipeCompletion := trailing_parser:minPrec " |>."

@[builtinTermParser] def subst := trailing_parser:75 " ▸ " >> sepBy1 (termParser 75) " ▸ "

-- NOTE: Doesn't call `categoryParser` directly in contrast to most other "static" quotations, so call `evalInsideQuot` explicitly
@[builtinTermParser] def funBinder.quot : Parser := leading_parser "`(funBinder|"  >> incQuotDepth (evalInsideQuot ``funBinder funBinder) >> ")"
def bracketedBinderF := bracketedBinder  -- no default arg
@[builtinTermParser] def bracketedBinder.quot : Parser := leading_parser "`(bracketedBinder|"  >> incQuotDepth (evalInsideQuot ``bracketedBinderF bracketedBinder) >> ")"
@[builtinTermParser] def matchDiscr.quot : Parser := leading_parser "`(matchDiscr|"  >> incQuotDepth (evalInsideQuot ``matchDiscr matchDiscr) >> ")"
@[builtinTermParser] def attr.quot : Parser := leading_parser "`(attr|"  >> incQuotDepth attrParser >> ")"

@[builtinTermParser] def panic       := leading_parser:leadPrec "panic! " >> termParser
@[builtinTermParser] def unreachable := leading_parser:leadPrec "unreachable!"
@[builtinTermParser] def dbgTrace    := leading_parser:leadPrec withPosition ("dbg_trace" >> ((interpolatedStr termParser) <|> termParser)) >> optSemicolon termParser
@[builtinTermParser] def assert      := leading_parser:leadPrec withPosition ("assert! " >> termParser) >> optSemicolon termParser


def macroArg       := termParser maxPrec
def macroDollarArg := leading_parser "$" >> termParser 10
def macroLastArg   := macroDollarArg <|> macroArg

-- Macro for avoiding exponentially big terms when using `STWorld`
@[builtinTermParser] def stateRefT   := leading_parser "StateRefT" >> macroArg >> macroLastArg

@[builtinTermParser] def dynamicQuot := leading_parser "`(" >> ident >> "|" >> incQuotDepth (parserOfStack 1) >> ")"

@[builtinTermParser] def dotIdent := leading_parser "." >> checkNoWsBefore >> rawIdent

end Term

@[builtinTermParser default+1] def Tactic.quot    : Parser := leading_parser "`(tactic|" >> incQuotDepth tacticParser >> ")"
@[builtinTermParser] def Tactic.quotSeq : Parser := leading_parser "`(tactic|" >> incQuotDepth Tactic.seq1 >> ")"

@[builtinTermParser] def Level.quot  : Parser := leading_parser "`(level|" >> incQuotDepth levelParser >> ")"

open Term in
builtin_initialize
  register_parser_alias letDecl
  register_parser_alias haveDecl
  register_parser_alias sufficesDecl
  register_parser_alias letRecDecls
  register_parser_alias hole
  register_parser_alias syntheticHole
  register_parser_alias matchDiscr
  register_parser_alias bracketedBinder
  register_parser_alias attrKind

end Parser
end Lean
