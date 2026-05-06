/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic
public import Lean.Parser.Term
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.FmtM.CommonFormatters
meta import Lean.Parser.Term
import Init.Data
import Init.While
import Lean.Fmt.FmtM.Comments

namespace Lean.Fmt

@[builtin_fmt num]
public def fmtNum : Fmt := fmtAtomic

@[builtin_fmt scientific]
public def fmtScientific : Fmt := fmtAtomic

namespace fmtStr

/-- A lexed element of the token of a non-raw string literal. -/
public inductive Element where
  /--
  A maximal run of non-whitespace characters, where each unit is a single character or escape
  sequence. When a word does not fit on a line, it may be split between two of its units by
  inserting a string gap.
  -/
  | word (units : Array String)
  /--
  A run of whitespace characters without newlines. Since a string gap consumes all whitespace at
  the start of the next line, whitespace must never be placed at the start of a line and is always
  glued to the content before it.
  -/
  | ws (s : String)
  /--
  A newline (escaped or literal, always rendered as `\n`), together with the whitespace directly
  following it. Newlines make the line structure of the string content explicit: a newline is
  placed at the start of the line that it introduces, with a string gap directly before it.
  Newlines at the start and at the end of the string do not separate two content lines and get no
  mandatory string gap. An escaped `\r` directly before the newline (`cr := true`) is part of a
  CRLF sequence and is kept together with the newline.
  -/
  | nl (cr : Bool) (post : String)
  /-- A string gap that was already present in the input and is retained as a hard line break. -/
  | gap
  /--
  An interpolation `{term}` of an interpolated string literal. Interpolations are flattened and
  treated like words, unless even placing the interpolation on its own line overflows the page
  width, in which case the interpolation is broken apart according to the formatting of `term`,
  with no other content surrounding it on its lines.
  -/
  | interp (term : Doc FmtCost)
deriving Inhabited

/--
Whether `c` is whitespace that a string gap consumes at the start of a line.
Mirrors `Lean.Parser.stringGapFn`.
-/
def isGapWhitespace (c : Char) : Bool := c.isWhitespace && c != '\n'

/--
Mirrors `Lean.Parser.isQuotableCharDefault`, plus `{`, which can only be escaped in interpolated
string literals (`Lean.Parser.isQuotableCharForStrInterpolant`). Since `\{` cannot occur in
non-interpolated string literals, it is safe to accept it for both.
-/
def isQuotableChar (c : Char) : Bool :=
  c == '\\' || c == '\"' || c == '\'' || c == 'r' || c == 'n' || c == 't' || c == '{'

def pushWordUnit (acc : Array Element) (unit : String) : Array Element :=
  if let some (.word units) := acc.back? then
    acc.set! (acc.size - 1) (.word (units.push unit))
  else
    acc.push (.word #[unit])

def pushWsChar (acc : Array Element) (c : Char) : Array Element :=
  match acc.back? with
  | some (.ws s) => acc.set! (acc.size - 1) (.ws (s.push c))
  | some (.nl cr post) => acc.set! (acc.size - 1) (.nl cr (post.push c))
  | _ => acc.push (.ws c.toString)

/--
Lexes the content of a (possibly interpolated) string literal token into `Element`s, appending
them to `acc`. `cs` must not include the delimiters of the token (the quotation marks, as well as
the braces delimiting the chunks of an interpolated string literal).
Yields `none` if the content is not well-formed.
-/
public partial def lex (cs : List Char) (acc : Array Element) : Option (Array Element) :=
  match cs with
  | [] =>
    some acc
  | '"' :: _ =>
    -- An unescaped quote cannot occur within the content of a string literal.
    none
  | '\\' :: '\n' :: cs =>
    -- A string gap consumes all whitespace at the start of the next line.
    lex (cs.dropWhile isGapWhitespace) (acc.push .gap)
  | '\\' :: 'n' :: cs =>
    lex cs (acc.push (.nl false ""))
  | '\\' :: 'x' :: c₁ :: c₂ :: cs =>
    lex cs (pushWordUnit acc ("\\x".push c₁ |>.push c₂))
  | '\\' :: 'u' :: c₁ :: c₂ :: c₃ :: c₄ :: cs =>
    lex cs (pushWordUnit acc ("\\u".push c₁ |>.push c₂ |>.push c₃ |>.push c₄))
  -- An escaped `\r` directly before a newline is part of a CRLF sequence and is kept together
  -- with the newline.
  | '\\' :: 'r' :: '\\' :: 'n' :: cs =>
    lex cs (acc.push (.nl true ""))
  | '\\' :: 'r' :: '\n' :: cs =>
    lex cs (acc.push (.nl true ""))
  | '\\' :: 'r' :: '\\' :: '\n' :: cs =>
    -- A string gap between the `\r` and a following `\n` (as produced by earlier versions of this
    -- formatter) is removed so that the CRLF sequence is kept together.
    match cs.dropWhile isGapWhitespace with
    | '\\' :: 'n' :: cs => lex cs (acc.push (.nl true ""))
    | cs => lex cs ((pushWordUnit acc "\\r").push .gap)
  | '\\' :: c :: cs =>
    if isQuotableChar c then
      lex cs (pushWordUnit acc ("\\".push c))
    else
      none
  | '\n' :: cs =>
    lex cs (acc.push (.nl false ""))
  | c :: cs =>
    if isGapWhitespace c then
      lex cs (pushWsChar acc c)
    else
      lex cs (pushWordUnit acc c.toString)

/--
Cost penalty for inserting a string gap at a word boundary. Only chosen when it reduces the
overflow over the page width; the penalty ensures that breaking the line outside of the string
(e.g. by moving the entire string to its own line) is preferred over splitting the string content.
-/
def softBreakPenalty : Nat := 1

/--
Cost penalty for moving a trailing newline of the string to the start of the next line.
Only chosen when it reduces the overflow over the page width.
-/
def anchorPenalty : Nat := 1

/--
Cost penalty for splitting a word between two of its units with a string gap. Only chosen when it
reduces the overflow over the page width; chosen after `anchorPenalty` alternatives.
-/
def wordSplitPenalty : Nat := 3

/--
Cost penalty for placing an interpolation of an interpolated string literal on its own line,
where it may be broken apart according to the formatting of the interpolated pattern.
Only chosen when it reduces the overflow over the page width; since keeping the interpolation
intact on its own line only costs the surrounding `softBreakPenalty` gaps, breaking apart the
interpolation is only chosen when the intact interpolation does not fit on a line by itself.
-/
def interpolationBreakPenalty : Nat := 3

/--
Cost penalty for omitting the mandatory string gap after a `\n`. This alternative exists so that
strings containing `\n` escapes can still be rendered on a single line in contexts that must be
flattened; the penalty ensures that it is never chosen otherwise.
-/
def noBreakPenalty : Nat := 1000

def penalized (amount : Nat) (d : Doc FmtCost) : Doc FmtCost :=
  .costing (DefaultCost.ofOverflowFallbackPenalty amount) d

/-- A string gap: `\` at the end of the current line, continuing on the next line. -/
def gapBreak : Doc FmtCost := .text "\\" ++ .hardNl

/-- A break opportunity at a word boundary before `rest`. -/
def softGapBreak (rest : Doc FmtCost) : Doc FmtCost :=
  .oneOf #[rest, penalized softBreakPenalty (.text "\\") ++ .hardNl ++ rest]

/-- Whether `e?` is an element that renders like a word: a word or an interpolation. -/
def isWordLike (e? : Option Element) : Bool :=
  e? matches some (.word ..) || e? matches some (.interp ..)

/--
Continues with `rest` after content that ends a line in the primary layout: if the next element
is a word or an interpolation, the current line may also be filled further.
-/
def continueAfterBreak (next? : Option Element) (rest : Doc FmtCost) : Doc FmtCost :=
  if isWordLike next? then
    softGapBreak rest
  else
    rest

/-- Renders a word before `rest`, offering to split it between units when the line overflows. -/
def buildWord (units : Array String) (rest : Doc FmtCost) : Doc FmtCost := Id.run do
  let mut acc := rest
  for i in (0...units.size) do
    let unit : Doc FmtCost := .text units[units.size - 1 - i]!
    if i != 0 then
      acc := .oneOf #[acc, penalized wordSplitPenalty (.text "\\") ++ .hardNl ++ acc]
    acc := unit ++ acc
  return acc

/-- Renders a newline and its trailing whitespace before `rest`. -/
def buildNl
    (cr : Bool) (post : String) (isLeading isTrailing prevIsGap : Bool) (next? : Option Element)
    (rest : Doc FmtCost)
    : Doc FmtCost :=
  let nlText : Doc FmtCost := .text ((if cr then "\\r\\n" else "\\n") ++ post)
  if isLeading then
    -- A newline at the start of the string does not separate two content lines, so it is kept
    -- together with the content following it and gets no mandatory break. Unlike elsewhere, a gap
    -- may also be inserted between two leading newlines so that a long run of leading newlines
    -- can still be broken when it overflows the line.
    let canBreak := isWordLike next? || next? matches some (.nl ..)
    nlText ++ (if canBreak then softGapBreak rest else rest)
  else if prevIsGap then
    -- The retained gap directly before this newline already broke the line before it, so the line
    -- containing this newline may be filled further.
    nlText ++ continueAfterBreak next? rest
  else if isTrailing then
    -- Like a leading newline, a newline at the end of the string does not separate two content
    -- lines and is kept together with the content before it, with optional gaps between two
    -- trailing newlines. When the line overflows, the newline may still be moved to the start of
    -- the next line.
    let canBreak := next? matches some (.nl ..)
    let glued := nlText ++ (if canBreak then softGapBreak rest else rest)
    .oneOf #[
      glued,
      penalized anchorPenalty (.text "\\") ++ .hardNl ++ glued
    ]
  else
    match next? with
    | some .gap =>
      -- The retained gap directly after this newline provides the mandatory break after it.
      nlText ++ rest
    | _ =>
      .oneOf #[
        -- The newline is placed at the start of the next line, before the content of the line
        -- that it introduces. When the newline and its content overflow the next line, the
        -- content can be broken again at its word boundaries, including directly after the
        -- newline and its trailing whitespace.
        gapBreak ++ nlText ++ continueAfterBreak next? rest,
        -- In contexts that must be flattened, the mandatory string gap can be omitted.
        penalized noBreakPenalty nlText ++ rest
      ]

/--
Renders an interpolation `{term}` before `rest`. `restAfterNext` is the rendering of the elements
after the next element, which is needed when the interpolation is broken apart and the following
whitespace run must be glued to it before the mandatory break after the interpolation.
-/
def buildInterp
    (term : Doc FmtCost) (prevIsGap : Bool) (next? nextNext? : Option Element)
    (rest restAfterNext : Doc FmtCost)
    : Doc FmtCost :=
  -- Primary: the interpolation is flattened and rendered like a word, filling the line together
  -- with the surrounding content. Together with the surrounding word boundaries, this also
  -- covers placing the intact interpolation on its own line.
  let inline := .join #[.text "{", .flattened term, .text "}"] ++ rest
  -- Fallback: the interpolation is placed on its own lines, without other content surrounding
  -- it, and may be broken apart according to the formatting of the interpolated pattern.
  let leadingBreak : Doc FmtCost :=
    if prevIsGap then
      -- The retained gap directly before the interpolation already broke the line before it.
      .empty
    else
      gapBreak
  let after : Doc FmtCost :=
    match next? with
    | some (.ws s) =>
      -- The following whitespace can never start a line and must remain glued to the
      -- interpolation, with the mandatory break after it (unless the element after it provides
      -- its own break).
      if isWordLike nextNext? then
        .text s ++ gapBreak ++ restAfterNext
      else
        .text s ++ restAfterNext
    | some (.word ..) | some (.interp ..) =>
      gapBreak ++ rest
    | _ =>
      -- A following newline or retained gap provides its own break; at the end of the string,
      -- the closing quote may follow directly after the interpolation.
      rest
  let alone :=
    .join #[
      leadingBreak,
      penalized interpolationBreakPenalty (.text "{"),
      term,
      .text "}",
      after
    ]
  .oneOf #[inline, alone]

/-- Renders the elements of a string literal, including the enclosing quotes. -/
public def build (elems : Array Element) : Doc FmtCost := Id.run do
  let isNlOrGap : Element → Bool := fun e => e matches .nl .. || e matches .gap
  -- A newline is leading/trailing if it is preceded/followed only by other newlines (and gaps
  -- inserted between them by a previous formatter run, which must remain in the leading/trailing
  -- regime for idempotence).
  let numLeading := elems.takeWhile isNlOrGap |>.size
  let numTrailing := elems.reverse.takeWhile isNlOrGap |>.size
  let mut rest : Doc FmtCost := .text "\""
  -- The rendering of the elements after the next element, i.e. `rest` from the iteration before
  -- the last one.
  let mut restAfterNext := rest
  for i in (0...elems.size) do
    let j := elems.size - 1 - i
    let next? := elems[j + 1]?
    let nextNext? := elems[j + 2]?
    let isLeading := j < numLeading
    let isTrailing := j >= elems.size - numTrailing
    let prevIsGap := j > 0 && elems[j - 1]! matches .gap
    let newRest :=
      match elems[j]! with
      | .word units => buildWord units rest
      | .ws s => .text s ++ continueAfterBreak next? rest
      | .nl cr post => buildNl cr post isLeading isTrailing prevIsGap next? rest
      | .gap => gapBreak ++ rest
      | .interp term => buildInterp term prevIsGap next? nextNext? rest restAfterNext
    restAfterNext := rest
    rest := newRest
  return .nested (.text "\"" ++ rest)

end fmtStr

/--
Formats a non-raw string literal by inserting string gaps at word boundaries when the string does
not fit within the page width, filling as many words as possible on each line. Newlines in the
string content (both `\n` escapes and literal newlines in multi-line strings) are made explicit
with a string gap followed by `\n` at the start of the line that the newline introduces. Newlines
at the start and at the end of the string are kept together with the content, and string gaps
that are already present in the input are retained. A single word that does not fit on a line on its own
is split with a string gap.
Raw string literals are retained as-is.
-/
@[builtin_fmt str]
public def fmtStr : Fmt := fun stx => do
  let some val := stx.isLit? strLitKind
    | throw .partialFormatter
  -- Raw string literals (`r"..."`) cannot contain string gaps and are retained as-is.
  if !(val.length >= 2 && val.startsWith "\"" && val.endsWith "\"") then
    return ← fmtAtomic stx
  let some elems := fmtStr.lex val.toList.tail.dropLast #[]
    | return ← fmtAtomic stx
  return Layouts.strLit empty <| ← taggedText (fmtStr.build elems) stx

@[builtin_fmt name]
public def fmtName : Fmt := fmtAtomic

@[builtin_fmt char]
public def fmtChar : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.quotedName]
public def fmtQuotedName : Fmt := fun
  | `(Parser.Term.quotedName| $n:name) => fmt n
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.paren]
public def fmtParen : Fmt := fun
  | `(Parser.Term.paren| (%$lbTk $t:term )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let t ← fmt t
    let rbTk ← fmt rbTk
    return Layouts.parens lbTk t rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.namedArgument]
public def fmtNamedArgument : Fmt := fun
  | `(Parser.Term.namedArgument| (%$lbTk $id:ident :=%$colonEqTk $body:term )%$rbTk) =>
    fmtNamedArgumentTerm lbTk id colonEqTk body rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.ellipsis]
public def fmtEllipsis : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.proj]
public def fmtProj : Fmt := fun
  | `($lhs:term.%$dotTk$field) => do
    let lhs ← fmt lhs
    fmtProjLike lhs dotTk field
  | _ =>
    throw .partialFormatter

@[builtin_fmt_sticky_term]
public def stickyIdRun : StickyTermFn := fun
  | `(Id.run) => true
  | _ => false

@[builtin_fmt Lean.Parser.Term.app]
public def fmtApp : Fmt := fun
  | `($fStx:term $args*) => do fmtAppLike <| #[fStx] ++ args
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.type]
public def fmtType : Fmt := fun
  | `(Parser.Term.type| Type%$typeTk) => fmt typeTk
  | `(Parser.Term.type| Type%$typeTk $level:level) => do fmtAppLike #[typeTk, level]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.sort]
public def fmtSort : Fmt := fun
  | `(Parser.Term.sort| Sort%$sortTk) => fmt sortTk
  | `(Parser.Term.sort| Sort%$sortTk $level:level) => do fmtAppLike #[sortTk, level]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.prop]
public def fmtProp : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.hygienicLParen]
public def fmtHygienicLParen : Fmt := fun
  | `(Parser.Term.hygienicLParen| (%$lbTk $_:hygieneInfo) => fmt lbTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.typeAscription]
public def fmtTypeAscription : Fmt := fun
  | `(Parser.Term.typeAscription|
      $lbTk:hygienicLParen $lhs:term :%$typeAscriptionTk $[$type?:term]? )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let lhs ← fmt lhs
    let typeAscriptionTk ← fmt typeAscriptionTk
    let type? ← fmt? type?
    let rbTk ← fmt rbTk
    let ascription := Layouts.typeAscription (format := .dense) lhs typeAscriptionTk type?
    return Layouts.parens lbTk ascription rbTk
  | _ =>
    throw .partialFormatter

@[builtin_infix_fmt Lean.Parser.Term.arrow]
public def fmtArrow : Fmt.InfixOperation :=
  -- The parser sets the node precedence to `maxPrec` and checks the actual precedence 25 with
  -- an inner `checkPrec`, so that `a → b` can be the left-hand side of any trailing parser.
  {
    sparse := true
    separateFinalOperand := true
    precs? := some { prec := 25, lhsPrec := 0, rhsPrec := 25 }
    extendedChainKinds := {``Parser.Term.depArrow}
  }

@[builtin_infix_fmt Lean.Parser.Term.depArrow]
public def fmtDepArrow : Fmt.InfixOperation := {
  sparse := true
  separateFinalOperand := true
  precs? := some { prec := 25, lhsPrec := 0, rhsPrec := 0 }
  extendedChainKinds := {``Parser.Term.arrow}
}

@[builtin_quantifier_fmt Lean.Parser.Term.forall]
public def fmtForall : QuantifierFmt := fun
  | `(Parser.Term.forall|
      ∀%$forallTk $binders* $[:%$typeAscriptionTk? $type?:term]? ,%$commaTk $body:term) =>
    some {
      quantifier := forallTk
      binders := .binders #[#[binders]]
      typeAscriptionTk?
      type?
      commaTk
      body
    }
  | _ =>
    none

@[builtin_fmt Lean.Parser.Term.explicit]
public def fmtExplicit : Fmt := fun
  | `(Parser.Term.explicit| @%$atTk$t:term) => do
    let atTk ← fmt atTk
    let t ← fmt t
    return Layouts.prefixOperator atTk t .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.cdot]
public def fmtCdot : Fmt
  -- `.` matches both `.` and `·`
  | `(Parser.Term.cdot| .%$dotTk $_:hygieneInfo) => fmt dotTk
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.borrowed]
public def fmtBorrowed : Fmt := fun
  | `(Parser.Term.borrowed| @&%$borrowTk $t:term) => do
    let borrowTk ← fmt borrowTk
    let t ← fmt t
    return Layouts.prefixOperator borrowTk t .withSpacing
  | _ =>
    throw .partialFormatter

meta def matchAlts := Lean.Parser.Term.matchAlts

@[builtin_fmt Lean.Parser.Term.fun]
public def fmtFun : Fmt := fun
  -- `fun%$funTk` also implicitly matches `λ` and `=>%$arrowTk` also matches `↦`.
  | `(Parser.Term.fun|
      fun%$funTk $binders:funBinder* $[ :%$typeAscriptionTk? $type? ]? =>%$arrowTk
        $body:term) => do
    let funTk ← fmt funTk
    let binders ← fmtArray binders
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let type? ← fmt? type?
    let arrowTk ← fmt arrowTk
    let body ← fmt body
    let signature := Layouts.localSignature #[] #[#[binders]] typeAscriptionTk? type?
    return Layouts.assignmentDeclaration (sticky := true) (Layouts.spacedAtomic #[funTk, signature])
      arrowTk body
  -- `fun%$funTk` also implicitly matches `λ`.
  | `(Parser.Term.fun| fun%$funTk $matchAlts:matchAlts) => do
    let isSingleMatchAlt := isSingleMatchAlt matchAlts
    let funTk ← fmt funTk
    let matchAlts ← fmt matchAlts
    if isSingleMatchAlt then
      return maybeFlattened <| combine #[
        .withSepAfter funTk ⟨nl, nested⟩,
        matchAlts
      ]
    let doc := Layouts.matchDeclaration funTk matchAlts
    return sticky doc doc .coequal
  | _ =>
    throw .partialFormatter
where
  isSingleMatchAlt : TSyntax ``Parser.Term.matchAlts → Bool
    | `(matchAlts| | $_ => $_) => true
    | _ => false

@[builtin_fmt Lean.Parser.Term.dotIdent]
public def fmtDotIdent : Fmt
  | `(Parser.Term.dotIdent| .%$dotTk$id:ident) => do
    let dotTk ← fmt dotTk
    let id ← fmt id
    return Layouts.prefixOperator dotTk id .withoutSpacing
  | _ =>
    throw .partialFormatter

public def fmtUniverseAnnotation?
    (lbTk? : Option Syntax) (levels? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let lbTk? ← fmt? lbTk?
  let levels := levels?.getD ⟨#[]⟩
  let levels ← fmtSepArray levels
  let rbTk? ← fmt? rbTk?
  return Layouts.collection lbTk? levels rbTk?

@[builtin_fmt Lean.Parser.Term.explicitUniv]
public def fmtExplicitUniv : Fmt := fun
  | `($lhs:term.{%$lbTk $levels,* }%$rbTk) => do
    let lhs ← fmt lhs
    let annotation? ← fmtUniverseAnnotation? lbTk levels rbTk
    return mkSelfDelimited <| Layouts.atomic #[lhs, annotation?]
  | _ =>
    throw .partialFormatter

public def fmtPipeProjLike
    (stx : Syntax) (deconstruct? : Syntax → FmtM (Option (Syntax × TaggedDoc)))
    : FmtM TaggedDoc := do
  let mut stx := stx
  let mut pipes := #[]
  while true do
    let some (stx', pipe) ← deconstruct? stx
      | break
    stx := stx'
    pipes := pipes.push pipe
  if pipes.isEmpty then
    throw .partialFormatter
  let lhs ← fmt stx
  pipes := pipes.reverse
  return nested <| Layouts.horizontalOrVertical <| #[hardNested lhs] ++ pipes

public def deconstructPipeProj : Syntax → FmtM (Option (Syntax × TaggedDoc))
  | `($stx':term |>.%$pipeProjTk$id$[.{%$lbTk? $levels?:level,* }%$rbTk?]? $args*) => do
    let pipeProjTk ← fmt pipeProjTk
    let id ← fmt id
    let universeAnnotation? ← fmtUniverseAnnotation? lbTk? levels? rbTk?
    let pipeHead :=
      Layouts.atomic #[
        pipeProjTk,
        id,
        universeAnnotation?
      ]
    let pipe ← fmtFixedApp pipeHead args
    return some (stx', pipe)
  | _ =>
    return none

@[builtin_fmt Lean.Parser.Term.pipeProj]
public def fmtPipeProj : Fmt := fun stx => fmtPipeProjLike stx deconstructPipeProj

@[builtin_infix_fmt Lean.Parser.Term.subst]
public def fmtSubst : Fmt.InfixOperation := {
  sparse := false
  precs? := some { prec := 75, lhsPrec := 0, rhsPrec := 75 }
}

@[builtin_fmt Lean.Parser.Term.anonymousCtor]
public def fmtAnonymousCtor : Fmt := fun
  | `(Parser.Term.anonymousCtor| ⟨%$lbTk $fields:term,* ⟩%$rbTk ) => do
    let lbTk ← fmt lbTk
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk fields rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.tuple]
public def fmtTuple : Fmt := fun
  | `(Parser.Term.tuple| (%$lbTk)%$rbTk) => do
    let lbTk ← fmt lbTk
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk (⟨#[]⟩ : SepArray ",") rbTk
  | `(Parser.Term.tuple| (%$lbTk $firstField:term ,%$firstCommaTk $fields:term,* )%$rbTk ) => do
    let lbTk ← fmt lbTk
    let fields : Syntax.TSepArray `term "," :=
      ⟨#[firstField.raw, firstCommaTk] ++ fields.elemsAndSeps⟩
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    return Layouts.tuple lbTk fields rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.namedPattern]
public def fmtNamedPattern : Fmt := fun
  | `($t1:term@%$atTk $[$id?:ident :%$typeAscriptionTk?]? $t2:term) => do
    let t1 ← fmt t1
    let atTk ← fmt atTk
    let id? ← fmt? id?
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let t2 ← fmt t2
    let rhs := Layouts.typeAscription id? typeAscriptionTk? t2
    return mkSelfDelimited <| Layouts.atomic #[t1, atTk, rhs]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letOptNondep]
public def fmtLetOptNondep := fmtAtomic

@[builtin_fmt Lean.Parser.Term.letOptPostponeValue]
public def fmtLetOptPostponeValue := fmtAtomic

@[builtin_fmt Lean.Parser.Term.letOptUsedOnly]
public def fmtLetOptUsedOnly := fmtAtomic

@[builtin_fmt Lean.Parser.Term.letOptZeta]
public def fmtLetOptZeta := fmtAtomic

@[builtin_fmt Lean.Parser.Term.letOptGeneralize]
public def fmtLetOptGeneralize := fmtAtomic

@[builtin_fmt Lean.Parser.Term.letOpts]
public def fmtLetOpts : Fmt := fun stx => do
  if stx.getKind != ``Parser.Term.letOpts then
    throw .partialFormatter
  let opt ← getStxArg! stx 0
  fmt opt

@[builtin_fmt Lean.Parser.Term.letPosOpt]
public def fmtLetPosOpt : Fmt
  | `(Parser.Term.letPosOpt| +%$plusTk$opt:letOpts) => do
    let plusTk ← fmt plusTk
    let opt ← fmt opt
    return Layouts.prefixOperator plusTk opt .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letNegOpt]
public def fmtLetNegOpt : Fmt := fun
  | `(Parser.Term.letNegOpt| -%$minusTk$opt:letOpts) => do
    let minusTk ← fmt minusTk
    let opt ← fmt opt
    return Layouts.prefixOperator minusTk opt .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letOptEq]
public def fmtLetOptEq : Fmt
  | `(Parser.Term.letOptEq| (%$lbTk eq%$eqTk :=%$colonEqTk $id )%$rbTk ) =>
    fmtNamedArgumentTerm lbTk eqTk colonEqTk id rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letConfig]
public def fmtLetConfig : Fmt := fun stx => do
  if stx.getKind != ``Parser.Term.letConfig then
    throw .partialFormatter
  let items ← getStxArg! stx 0
  let items ← items.getArgs.mapM fmt
  return Layouts.fill items

public def fmtLetTerm
    (keywordTk : Syntax) (config? : Option (TSyntax ``Parser.Term.letConfig))
    (decl : TSyntax ``Parser.Term.letDecl) (semicolonTk : Syntax) (body : TSyntax `term)
    : FmtM TaggedDoc := do
  let components := #[keywordTk] ++ config?.toArray ++ #[decl]
  let keywordTk ← fmt keywordTk
  let config? ← fmt? config?
  let decl ← fmt decl
  let fullDecl := Layouts.letDecl keywordTk config? decl
  fmtTermInstruction fullDecl components semicolonTk body

@[builtin_fmt Lean.Parser.Term.let]
public def fmtLet : Fmt := fun
  | `(Parser.Term.let|
      let%$letTk $config:letConfig $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm letTk config decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.have]
public def fmtHave : Fmt := fun
  | `(Parser.Term.have|
      have%$haveTk $config:letConfig $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm haveTk config decl semicolonTk body
  | _ =>
    throw .partialFormatter

public def fmtLetRecDecl (compact : Bool) : Fmt := fun
  | `(Parser.Term.letRecDecl|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $letDecl:letDecl
      $terminationSuffix:suffix) => do
    let docComment? ← fmt? docComment?
    let letDecl ← fmt letDecl
    -- May be `empty`
    let terminationSuffix ← fmt terminationSuffix
    let declWithAttributes ← fmtDeclWithAttributes attributes? letDecl compact
    return Layouts.lines #[docComment?, declWithAttributes, terminationSuffix]
  | _ =>
    throw .partialFormatter

public def fmtLetRecDecls (compact : Bool) : Fmt := fun
  | `(Parser.Term.letRecDecls| $decls:letRecDecl,*) => do
    let decls ← fmtTSepArrayWith (fmtLetRecDecl compact) ``fmtLetRecDecl decls
    return Layouts.sepLines decls (includeSeps := true)
  | _ =>
    throw .partialFormatter

public def fmtFullLetRecDecl (tks : Array Syntax) (decls : TSyntax ``Parser.Term.letRecDecls)
    : FmtM TaggedDoc := do
  let tks ← tks.mapM fmt
  let kwTks := Layouts.spacedAtomic tks
  let isSimpleDecl ← isSimpleDecl decls
  let decls ← fmtWith (fmtLetRecDecls (compact := true)) ``fmtLetRecDecls decls
  return Layouts.letDecl kwTks empty decls { separateSignatureAndDecl := !isSimpleDecl }
where
  isSimpleDecl : TSyntax `Lean.Parser.Term.letRecDecls → FmtM Bool
    | `(Parser.Term.letRecDecls| $[$_:attributes]? $_:letDecl $[$_]?) => return true
    | _ => return false

@[builtin_fmt Lean.Parser.Term.letrec]
public def fmtLetrec : Fmt := fun
  | `(Parser.Term.letrec| let%$letTk rec%$recTk $decls:letRecDecls ;%$semicolonTk $body:term) => do
    let components := #[letTk, recTk, decls]
    let fullDecl ← fmtFullLetRecDecl #[letTk, recTk] decls
    fmtTermInstruction fullDecl components semicolonTk body
  | _ =>
    throw .partialFormatter
where
  isSimpleDecl : TSyntax `Lean.Parser.Term.letRecDecls → FmtM Bool
    | `(Parser.Term.letRecDecls| $[$_:attributes]? $_:letDecl $[$_]?) => return true
    | _ => return false

@[builtin_fmt Lean.Parser.Term.byTactic]
public def fmtByTactic : Fmt := fun
  | `(Lean.Parser.Term.byTactic| by%$byTk $tacticSeq:tacticSeq) => do
    let byTk ← fmt byTk
    let tacticSeq ← fmt tacticSeq
    return Layouts.keywordPrefixedSeq byTk tacticSeq .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.show]
public def fmtShow : Fmt := fun
  | `(Parser.Term.show| show%$showTk $goal:term from%$fromTk $proof:term) => do
    let showTk ← fmt showTk
    let goal ← fmt goal
    let lhs := Layouts.pseudoApplication #[showTk, goal]
    let fromTk ← fmt fromTk
    let proof ← fmt proof
    return Layouts.keywordSeparated lhs fromTk proof
  | `(Parser.Term.show| show%$showTk $goal:term by%$byTk $tacticSeq:tacticSeq) => do
    let showTk ← fmt showTk
    let goal ← fmt goal
    let lhs := Layouts.pseudoApplication #[showTk, goal]
    let byTk ← fmt byTk
    let tacticSeq ← fmt tacticSeq
    return Layouts.keywordSeparated lhs byTk tacticSeq
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.matchDiscr]
public def fmtMatchDiscr : Fmt
  | `(Parser.Term.matchDiscr| $[$id? :%$colonTk?]? $discr:term) => do
    let id? ← fmt? id?
    let colonTk? ← fmt? colonTk?
    let discr ← fmt discr
    return Layouts.typeAscription id? colonTk? discr
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.trueVal]
public def fmtTrueVal : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.falseVal]
public def fmtFalseVal : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.generalizingParam]
public def fmtGeneralizingParam : Fmt := fun
  | `(Parser.Term.generalizingParam| (%$lbTk generalizing%$generalizingTk :=%$colonEqTk $flag )%$rbTk) =>
    fmtNamedArgumentTerm lbTk generalizingTk colonEqTk flag rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.motive]
public def fmtMotive : Fmt := fun
  | `(Parser.Term.motive| (%$lbTk motive%$motiveTk :=%$colonEqTk $rhs:term )%$rbTk) =>
    fmtNamedArgumentTerm lbTk motiveTk colonEqTk rhs rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.match]
public def fmtMatch : Fmt := fun
  | `(Parser.Term.match|
      match%$matchTk $[$generalizingParam?:generalizingParam]? $[$motive?:motive]? $matchDiscrs:matchDiscr,* with%$withTk
      $matchAlts:matchAlts) => do
    let matchTk ← fmt matchTk
    let generalizingParam? ← fmt? generalizingParam?
    let motive? ← fmt? motive?
    let matchLhs := Layouts.pseudoApplication #[matchTk, generalizingParam?, motive?]
    let matchDiscrs ← fmtTSepArray matchDiscrs
    let withTk ← fmt withTk
    let matchAlts ← fmt matchAlts
    let «match» := Layouts.keywordPrefixedSepFill matchLhs matchDiscrs .nonSticky
    return Layouts.keywordSeparated «match» withTk matchAlts {
      allowFlattening := false
      nestedRhs := false
    }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.docComment]
public def fmtDocComment : Fmt := fun stx => do
  let ctx ← read
  let some range := stx.getRange?
    | throw <| .elaboration <| .malformedInputSyntax stx "missing range on comment syntax"
  let some pos := ctx.text.source.pos? range.start
    | throw <| .elaboration <|
        .malformedInputSyntax stx "malformed start position on comment syntax"
  let some tailPos := ctx.text.source.pos? range.stop
    | throw <| .elaboration <| .malformedInputSyntax stx "malformed stop position on comment syntax"
  let body := ctx.text.source.extract pos tailPos
  let lineInfo ← getLineInfo! range.start
  let posInLine := range.start.unoffsetBy lineInfo.startPos
  let startColumnOffset := posInLine.offsetOfPos lineInfo.line
  let content := normalizeCommentContent body "/--" "-/" startColumnOffset (isLineComment := false)
  let lines := content.map (untagged <| .text ·)
  let s := untagged <| .text "/--"
  let c := joinUsing hardNl lines
  let e := untagged <| .text "-/"
  let r := Layouts.horizontalOrVertical #[s, c, e]
  tag r stx

@[builtin_fmt Lean.Parser.Term.attrKind]
public def fmtAttrKind : Fmt := fun
  | `(Parser.Term.attrKind| $[scoped%$scopedTk?]?) => fmt? scopedTk?
  | `(Parser.Term.attrKind| $[local%$localTk?]?) => fmt? localTk?
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.attrInstance]
public def fmtAttrInstance : Fmt := fun
  | `(Parser.Term.attrInstance| $kind:attrKind $attr:attr) => do
    let kind ← fmt kind
    let attr ← fmt attr
    return nested <| combine #[.withSepAfter kind space, attr]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.attributes]
public def fmtAttributes : Fmt := fun
  | `(Parser.Term.attributes| @[%$attrLbTk $attrInstances:attrInstance,* ]%$attrRbTk) => do
    let attrLbTk ← fmt attrLbTk
    let attrInstances ← fmtTSepArray attrInstances
    let attrRbTk ← fmt attrRbTk
    let attrInstances := Layouts.sepFill attrInstances
    return Layouts.bracketed attrLbTk attrInstances attrRbTk .dense
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Termination.terminationBy?]
public def fmtTerminationBy? : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Termination.terminationBy]
public def fmtTerminationBy : Fmt := fun
  | `(Parser.Termination.terminationBy|
      termination_by%$terminationByTk $[structural%$structuralTk?]? $[$ids?* =>%$arrowTk?]?
        $measure:term) => do
    let terminationByTk ← fmt terminationByTk
    let structuralTk? ← fmt? structuralTk?
    let tks := Layouts.spacedAtomic #[terminationByTk, structuralTk?]
    let ids ← fmtArray (ids?.getD #[])
    let signature := Layouts.pseudoApplication <| #[tks] ++ ids
    let arrowTk? ← fmt? arrowTk?
    let measure ← fmt measure
    return Layouts.assignmentDeclaration signature arrowTk? measure
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Termination.partialFixpoint]
public def fmtPartialFixpoint : Fmt := fun
  | `(Parser.Termination.partialFixpoint|
      partial_fixpoint%$partialFixpointTk $[monotonicity%$monotonicityTk? $proof?:term]?) => do
    let partialFixpoint ← fmt partialFixpointTk
    let monotonicity? ← fmt? monotonicityTk?
    let kws := Layouts.spacedAtomic #[partialFixpoint, monotonicity?]
    let proof? ← fmt? proof?
    return Layouts.pseudoApplication #[kws, proof?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Termination.coinductiveFixpoint]
public def fmtCoinductiveFixpoint : Fmt := fun
  | `(Parser.Termination.coinductiveFixpoint|
      coinductive_fixpoint%$coinductiveFixpointTk $[monotonicity%$monotonicityTk? $proof?:term]?) =>
    do
      let coinductiveFixpoint ← fmt coinductiveFixpointTk
      let monotonicity? ← fmt? monotonicityTk?
      let kws := Layouts.spacedAtomic #[coinductiveFixpoint, monotonicity?]
      let proof? ← fmt? proof?
      return Layouts.pseudoApplication #[kws, proof?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Termination.inductiveFixpoint]
public def fmtInductiveFixpoint : Fmt := fun
  | `(Parser.Termination.inductiveFixpoint|
      inductive_fixpoint%$inductiveFixpointTk $[monotonicity%$monotonicityTk? $proof?:term]?) => do
    let inductiveFixpoint ← fmt inductiveFixpointTk
    let monotonicity? ← fmt? monotonicityTk?
    let kws := Layouts.spacedAtomic #[inductiveFixpoint, monotonicity?]
    let proof? ← fmt? proof?
    return Layouts.pseudoApplication #[kws, proof?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Termination.suffix]
public def fmtTerminationSuffix : Fmt := fun
  | `(Parser.Termination.suffix|
      $[$terminationBy?]?
      $[decreasing_by%$decreasingByTk? $decreasingByTacticSeq?:tacticSeq]?) => do
    let terminationBy? ← fmt? terminationBy?
    let decreasingBy? ← fmt? decreasingByTk?
    let decreasingByTacticSeq? ← fmt? decreasingByTacticSeq?
    let decreasingBy := Layouts.keywordPrefixedSeq decreasingBy? decreasingByTacticSeq? .nonSticky
    return Layouts.lines #[terminationBy?, decreasingBy]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letId]
public def fmtLetId : Fmt
  | `(Parser.Term.letId| _%$holeTk) => fmt holeTk
  | `(Parser.Term.letId| $id:ident) => fmt id
  | `(Parser.Term.letId| $s:hygieneInfo) => fmt s
  | _ => throw .partialFormatter

public def convertLetIdBinders (binders : TSyntaxArray ``Parser.Term.letIdBinder)
    : TSyntaxArray binderKinds :=
  binders.map fun
    | `(Parser.Term.letIdBinder| $id:ident) => id
    | `(Parser.Term.letIdBinder| $hole:hole) => hole
    | `(Parser.Term.letIdBinder| $bracketedBinder:bracketedBinder) => bracketedBinder

public def convertBracketedBinders (binders : TSyntaxArray ``Parser.Term.bracketedBinder)
    : TSyntaxArray binderKinds :=
  binders.map fun
    | `(Parser.Term.bracketedBinderF| $bracketedBinder:bracketedBinder) => bracketedBinder

@[builtin_fmt Lean.Parser.Term.letIdDecl]
public def fmtLetIdDecl : Fmt := fun
  | `(Parser.Term.letIdDecl|
      $letId:letId $letIdBinders:letIdBinder* $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk
        $body:term) => do
    let letIdBinders := convertLetIdBinders letIdBinders
    let signature ← fmtLocalSignature letId letIdBinders typeAscriptionTk? type?
    let colonEqTk ← fmt colonEqTk
    let body ← fmt body
    return Layouts.assignmentDeclaration signature colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letEqnsDecl]
public def fmtLetEqnsDecl : Fmt := fun
  | `(Parser.Term.letEqnsDecl|
      $letId:letId $letIdBinders:letIdBinder* $[:%$typeAscriptionTk? $type?:term]?
      $matchAlts:matchAlts) => do
    let letIdBinders := convertLetIdBinders letIdBinders
    let signature ← fmtLocalSignature letId letIdBinders typeAscriptionTk? type?
    let matchAlts ← fmt matchAlts
    return Layouts.matchDeclaration signature matchAlts
  | _ =>
    throw .partialFormatter

meta def letPatDeclF := Parser.Term.letPatDecl

public def fmtPatSignature
    (pat : TSyntax `term) (typeAscriptionTk? : Option Syntax) (type? : Option (TSyntax `term))
    : FmtM TaggedDoc := do
  let pat ← fmt pat
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.localSignature #[pat] #[] typeAscriptionTk? type?

@[builtin_fmt Lean.Parser.Term.letPatDecl]
public def fmtLetPatDecl : Fmt := fun
  | `(letPatDeclF| $pat:term $[:%$typeAscriptionTk? $type?:term]? :=%$colonEqTk $body:term) => do
    let signature ← fmtPatSignature pat typeAscriptionTk? type?
    let colonEqTk ← fmt colonEqTk
    let body ← fmt body
    return Layouts.assignmentDeclaration signature colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letDecl]
public def fmtLetDecl : Fmt := fun
  | `(Parser.Term.letDecl| $letIdDecl:letIdDecl) => fmt letIdDecl
  | `(Parser.Term.letDecl| $letEqnsDecl:letEqnsDecl) => fmt letEqnsDecl
  | `(Parser.Term.letDecl| $letPatDecl:letPatDecl) => fmt letPatDecl
  | _ => throw .partialFormatter

-- This feature is currently not implemented in the elaborator
-- since it is not finalized, so we just raw-format it for now.
@[builtin_fmt Lean.Parser.Term.whereFinallySubsection]
public def fmtWhereFinallySubsection : Fmt := fmtRaw

@[builtin_fmt Lean.Parser.Term.whereFinally]
public def fmtWhereFinally : Fmt := fun
  | `(Lean.Parser.Term.whereFinally|
      finally%$finallyTk $tacticSeq:tacticSeq $whereFinallyAlts:whereFinallySubsection*) => do
    let finallyTk ← fmt finallyTk
    let tacticSeq ← fmt tacticSeq
    let whereFinallyAlts ← fmtArray whereFinallyAlts
    let hasWhereFinallyAlts := !whereFinallyAlts.isEmpty
    let whereFinallyAlts := Layouts.lines whereFinallyAlts
    if hasWhereFinallyAlts then
      let mainFinally := Layouts.keywordPrefixedSeq finallyTk tacticSeq .sticky
      -- This formatting is really ugly, but this is because the syntax itself is really ugly
      return combine #[
        .withSepAfter (hardNested mainFinally) ⟨hardNl, nested⟩,
        whereFinallyAlts
      ]
    else
      return Layouts.keywordPrefixedSeq finallyTk tacticSeq .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.whereDecls]
public def fmtWhereDecls : Fmt := fun
  | `(Parser.Term.whereDecls| where%$whereTk $declsAndSeps:letRecDecl;* $[$whereFinally?:whereFinally]?) =>
    do
      let whereTkTrailing ← fmtTrailingWithRetainedNewlinesAndComments whereTk
      let declsTrailing ← fmtTrailingWithRetainedNewlinesAndComments (mkNullNode declsAndSeps)
      let whereTk ← fmt whereTk
      let decls := declsAndSeps.getElems
      let whereFinally? ← fmt? whereFinally?
      if decls.isEmpty then
        return Layouts.spacedAtomic #[whereTk, whereFinally?]
      let decls ←
        fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith
          (fmtWith (fmtLetRecDecl (compact := false)) ``fmtLetRecDecl) decls
      let whereDecls := nested <| Layouts.retainedWhitespace #[whereTk, whereTkTrailing, decls]
      return Layouts.retainedWhitespace #[whereDecls, declsTrailing, whereFinally?]
  | _ =>
    throw .partialFormatter

public def isComplexAlt (stx : Syntax) : FmtM Bool := do
  let `(Parser.Term.matchAltExpr| | $[$_:term,*]|* => $_:term) := stx
    | throw .partialFormatter
  let patss := stx[1].getArgs.map (·.getArgs)
  return patss.any (·.size > 1)

public def fmtMatchAlt (stx : Syntax) : FmtM Layouts.Types.Alt := do
  -- The following anti-quotation does not retain the `|` separators,
  -- so we deconstruct the syntax manually.
  let `(Parser.Term.matchAltExpr| | $[$_:term,*]|* => $_:term) := stx
    | throw .partialFormatter
  let initialAltTk := stx[0]
  let patss := stx[1].getArgs
  let arrowTk := stx[2]
  let rhs := stx[3]
  let isComplexAlt ← isComplexAlt stx
  let initialAltTk ← fmt initialAltTk
  let patss : SepArray "|" ←
    patss.mapIdxM fun i patsOrSep => do
      if i % 2 == 0 then
        let pats : SepArray "," ← patsOrSep.getArgs.mapM fmt
        return Layouts.sepFill pats
      else
        fmt patsOrSep
  let patss := joinAltPats initialAltTk patss
  let arrowTk ← fmt arrowTk
  let rhs ← fmt rhs
  return Layouts.alt patss arrowTk rhs isComplexAlt

@[builtin_fmt Lean.Parser.Term.matchAlts]
public def fmtMatchAlts : Fmt := fun
  | `(matchAlts| $matchAlts:matchAlt*) => do
    let isComplexMatch := matchAlts.size > 1 && (← matchAlts.anyM isComplexAlt)
    let matchAlts ← matchAlts.mapM fmtMatchAlt
    return Layouts.alts matchAlts (allowFlattenedAlts := !isComplexMatch)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.structInstFieldDef]
public def fmtStructInstFieldDef : Fmt := fun
  | `(Parser.Term.structInstFieldDef| :=%$colonEqTk $[private%$privateTk?]? $body:term) => do
    let colonEqTk ← fmt colonEqTk
    let privateTk? ← fmt? privateTk?
    let separator := Layouts.spacedAtomic #[colonEqTk, privateTk?]
    let body ← fmt body
    return mkStructInstFieldDecl fun signature =>
      Layouts.assignmentDeclaration signature separator body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.structInstFieldEqns]
public def fmtStructInstFieldEqns : Fmt := fun
  | `(Parser.Term.structInstFieldEqns| $[private%$privateTk?]? $matchAlts:matchAlts) => do
    let privateTk? ← fmt? privateTk?
    let matchAlts ← fmt matchAlts
    return mkStructInstFieldDecl fun signature =>
      let signature := Layouts.spacedAtomic #[signature, privateTk?]
      Layouts.matchDeclaration signature matchAlts
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.optEllipsis]
public def fmtOptEllipsis : Fmt := fmtAtomic

public def fmtSetNotationLike (lbTk : Syntax) (elems : Syntax.TSepArray ks ",") (rbTk : Syntax)
    : FmtM TaggedDoc := do
  fmtArrayLit lbTk elems rbTk

@[builtin_fmt Lean.Parser.Term.structInst]
public def fmtStructInst : Fmt := fun
  | stx@`(Parser.Term.structInst| {%$lbTk $[$_:structInstLVal],* }%$rbTk) => do
    let lbTk ← fmt lbTk
    let `({ $fields:structInstField,* }) := stx
      | throw .partialFormatter
    let fields ← fmtSepArray (sep := ",") fields
    let rbTk ← fmt rbTk
    let fields := Layouts.sepArray fields <| .joinUsingSep none nl
    return Layouts.bracketed lbTk fields rbTk <| .sparse nl (stickynessKind := .preferSticky)
  | `(Parser.Term.structInst| {%$lbTk
        $[$modifiedStructures?:term,* with%$withTk?]?
        $fields:structInstField,* $optEllipsis:optEllipsis
        $[:%$typeAscriptionTk? $type?:term]?
      }%$rbTk ) => do
    let lbTk ← fmt lbTk
    let modifiedStructures := modifiedStructures?.getD ⟨#[]⟩
    let modifiedStructures ← fmtTSepArray modifiedStructures
    let withTk? ← fmt? withTk?
    let typeAscriptionTk? ← fmt? typeAscriptionTk?
    let type? ← fmt? type?
    let rbTk ← fmt rbTk
    let mut fields ←
      fields.elemsAndSeps.mapIdxM fun i elemOrSep => do
        if i % 2 = 0 then
          fmt elemOrSep
        else if i < fields.elemsAndSeps.size - 1 then
          -- Hack: We deliberately do not tag the separator here.
          -- We need this `.newline ", "` construct so that we can surrender the
          -- decision of whether to flatten the entire structure instance or not
          -- to `Layouts.bracketed`, but we cannot tag it because doing so
          -- would tag the newline itself in the alternative where the instance is not flattened,
          -- which means that e.g. comments would then get associated with the newline instead of
          -- a proper token.
          -- The comment re-association heuristic already does the right thing here when this is
          -- left untagged.
          -- If we ever really want to transfer meta-data precisely for these separators,
          -- we'd likely have to write a custom bracketing layouter for structure instances that
          -- only tags the separators in the alternative where they are flattened and appear in
          -- the output.
          return untagged (.newline ", ")
        else
          return empty
    let optEllipsis ← fmt optEllipsis
    if !optEllipsis.isAlwaysEmpty then
      if !fields.isEmpty then
        fields := fields.push <| untagged <| .newline ", "
      fields := fields.push optEllipsis
    let modifiedStructures :=
      Layouts.sepHorizontalOrVertical modifiedStructures (includeSeps := true)
    let withSignature := Layouts.spacedAtomic #[modifiedStructures, withTk?]
    let typeSignature := Layouts.prefixOperator typeAscriptionTk? type? .withSpacing
    let body :=
      combine #[
        .withSepAfter withSignature nl,
        .withSepAfter (withPosition (join fields)) nl,
        typeSignature
      ]
    return Layouts.bracketed lbTk body rbTk <| .sparse nl (stickynessKind := .preferSticky)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.inferInstanceAs]
public def fmtInferInstanceAs : Fmt := fun stx => do
  if stx.getNumArgs != 2 && stx.getNumArgs != 3 then
    throw .partialFormatter
  let inferInstanceAsTk ← getStxArg! stx 0
  let (pipeTk?, type) ←
    if stx.getNumArgs == 2 then
      pure (none, ← getStxArg! stx 1)
    else
      pure (some <| ← getStxArg! stx 1, ← getStxArg! stx 2)
  let inferInstanceAsTk ← fmt inferInstanceAsTk
  let pipeTk? ← fmt? pipeTk?
  let type ← fmt type
  return Layouts.pipeOperator #[inferInstanceAsTk, pipeTk?, type]

@[builtin_fmt Lean.Parser.Term.privateDecl]
public def fmtPrivateDecl : Fmt := fun
  | `(Parser.Term.privateDecl| private_decl%%$privateDeclTk $t:term) => do
    fmtAppLike #[privateDeclTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.sorry]
public def fmtSorry : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.unreachable]
public def fmtUnreachable : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.nofun]
public def fmtNofun : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.declName]
public def fmtDeclName : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.structInstDefault]
public def fmtStructInstDefault : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.doubleQuotedName]
public def fmtDoubleQuotedName : Fmt := fun stx => do
  let backtick1 ← fmt (← getStxArg! stx 0)
  let backtick2 ← fmt (← getStxArg! stx 1)
  let id ← fmt (← getStxArg! stx 2)
  return Layouts.atomic #[backtick1, backtick2, id]

@[builtin_fmt Lean.Parser.Term.completion]
public def fmtCompletion : Fmt := fun stx => do
  if stx.getKind != ``Parser.Term.completion then
    throw .partialFormatter
  let lhs ← fmt (← getStxArg! stx 0)
  let dotTk ← fmt (← getStxArg! stx 1)
  return mkSelfDelimited <| Layouts.atomic #[lhs, dotTk]

@[builtin_fmt Lean.Parser.Term.pipeCompletion]
public def fmtPipeCompletion : Fmt := fun stx => do
  if stx.getKind != ``Parser.Term.pipeCompletion then
    throw .partialFormatter
  let lhs ← fmt (← getStxArg! stx 0)
  let pipeTk ← fmt (← getStxArg! stx 1)
  return Layouts.spacedAtomic #[lhs, pipeTk]

@[builtin_fmt Lean.Parser.Term.unsafe]
public def fmtUnsafeTerm : Fmt := fun
  | `(Parser.Term.unsafe| unsafe%$unsafeTk $t:term) => do fmtAppLike #[unsafeTk, t]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.panic]
public def fmtPanic : Fmt := fun
  | `(Parser.Term.panic| panic!%$panicTk $t:term) => do fmtAppLike #[panicTk, t]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.noindex]
public def fmtNoindex : Fmt := fun
  | `(Parser.Term.noindex| no_index%$noIndexTk $t:term) => do fmtAppLike #[noIndexTk, t]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.binop]
public def fmtBinop : Fmt := fun
  | `(Parser.Term.binop| binop%%$binopTk $f:ident $a:term $b:term) => fmtAppLike #[binopTk, f, a, b]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.binop_lazy]
public def fmtBinopLazy : Fmt := fun
  | `(Parser.Term.binop_lazy| binop_lazy%%$binopTk $f:ident $a:term $b:term) => do
    fmtAppLike #[binopTk, f, a, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.binrel]
public def fmtBinrel : Fmt := fun
  | `(Parser.Term.binrel| binrel%%$binrelTk $f:ident $a:term $b:term) => do
    fmtAppLike #[binrelTk, f, a, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.binrel_no_prop]
public def fmtBinrelNoProp : Fmt := fun
  | `(Parser.Term.binrel_no_prop| binrel_no_prop%%$binrelTk $f:ident $a:term $b:term) => do
    fmtAppLike #[binrelTk, f, a, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.leftact]
public def fmtLeftact : Fmt := fun
  | `(Parser.Term.leftact| leftact%%$leftactTk $f:ident $a:term $b:term) => do
    fmtAppLike #[leftactTk, f, a, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.rightact]
public def fmtRightact : Fmt := fun
  | `(Parser.Term.rightact| rightact%%$rightactTk $f:ident $a:term $b:term) => do
    fmtAppLike #[rightactTk, f, a, b]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.unop]
public def fmtUnop : Fmt := fun
  | `(Parser.Term.unop| unop%%$unopTk $f:ident $a:term) => do fmtAppLike #[unopTk, f, a]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.forInMacro]
public def fmtForInMacro : Fmt := fun
  | `(Parser.Term.forInMacro| for_in%%$forInTk $a:term $b:term $c:term) => do
    fmtAppLike #[forInTk, a, b, c]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.forInMacro']
public def fmtForInMacro' : Fmt := fun
  | `(Parser.Term.forInMacro'| for_in'%%$forInTk $a:term $b:term $c:term) => do
    fmtAppLike #[forInTk, a, b, c]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.typeOf]
public def fmtTypeOf : Fmt := fun
  | `(Parser.Term.typeOf| type_of%%$typeOfTk $t:term) => do fmtAppLike #[typeOfTk, t]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.ensureTypeOf]
public def fmtEnsureTypeOf : Fmt := fun
  | `(Parser.Term.ensureTypeOf| ensure_type_of%%$ensureTypeOfTk $t:term $s:str $body:term) => do
    fmtAppLike #[ensureTypeOfTk, t, s, body]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.ensureExpectedType]
public def fmtEnsureExpectedType : Fmt := fun
  | `(Parser.Term.ensureExpectedType| ensure_expected_type%%$ensureExpectedTypeTk $s:str $t:term) =>
    do fmtAppLike #[ensureExpectedTypeTk, s, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.noImplicitLambda]
public def fmtNoImplicitLambda : Fmt := fun
  | `(Parser.Term.noImplicitLambda| no_implicit_lambda%%$noImplicitLambdaTk $t:term) => do
    fmtAppLike #[noImplicitLambdaTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.valueOf]
public def fmtValueOf : Fmt := fun
  | `(Parser.Term.valueOf| value_of%%$valueOfTk $id:ident) => do fmtAppLike #[valueOfTk, id]
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.showTermElabImpl]
public def fmtShowTermElabImpl : Fmt := fun
  | `(Parser.Term.showTermElabImpl| show_term_elab%$showTermElabTk $t:term) => do
    fmtAppLike #[showTermElabTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.defaultOrOfNonempty]
public def fmtDefaultOrOfNonempty : Fmt := fun
  | `(Parser.Term.defaultOrOfNonempty| default_or_ofNonempty%%$defaultOrTk $[unsafe%$unsafeTk?]?) =>
    do
      let defaultOrTk ← fmt defaultOrTk
      let unsafeTk? ← fmt? unsafeTk?
      return Layouts.spacedAtomic #[defaultOrTk, unsafeTk?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.noErrorIfUnused]
public def fmtNoErrorIfUnused : Fmt := fun
  | `(Parser.Term.noErrorIfUnused| no_error_if_unused%%$noErrorTk $t:term) => do
    fmtAppLike #[noErrorTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.throwNamedErrorMacro]
public def fmtThrowNamedErrorMacro : Fmt := fun
  | `(Parser.Term.throwNamedErrorMacro| throwNamedError%$throwTk $name:ident $msg) => do
    fmtAppLike #[throwTk, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.throwNamedErrorAtMacro]
public def fmtThrowNamedErrorAtMacro : Fmt := fun
  | `(Parser.Term.throwNamedErrorAtMacro| throwNamedErrorAt%$throwTk $ref:term $name:ident $msg) =>
    do fmtAppLike #[throwTk, ref, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.logNamedErrorMacro]
public def fmtLogNamedErrorMacro : Fmt := fun
  | `(Parser.Term.logNamedErrorMacro| logNamedError%$logTk $name:ident $msg) => do
    fmtAppLike #[logTk, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.logNamedErrorAtMacro]
public def fmtLogNamedErrorAtMacro : Fmt := fun
  | `(Parser.Term.logNamedErrorAtMacro| logNamedErrorAt%$logTk $ref:term $name:ident $msg) => do
    fmtAppLike #[logTk, ref, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.logNamedWarningMacro]
public def fmtLogNamedWarningMacro : Fmt := fun
  | `(Parser.Term.logNamedWarningMacro| logNamedWarning%$logTk $name:ident $msg) => do
    fmtAppLike #[logTk, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.logNamedWarningAtMacro]
public def fmtLogNamedWarningAtMacro : Fmt := fun
  | `(Parser.Term.logNamedWarningAtMacro| logNamedWarningAt%$logTk $ref:term $name:ident $msg) => do
    fmtAppLike #[logTk, ref, name, msg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.inaccessible]
public def fmtInaccessible : Fmt := fun
  | `(Parser.Term.inaccessible| .(%$lbTk $t:term )%$rbTk) => do
    let lbTk ← fmt lbTk
    let t ← fmt t
    let rbTk ← fmt rbTk
    return Layouts.bracketed lbTk t rbTk .dense
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.dbgTrace]
public def fmtDbgTrace : Fmt := fun
  | `(Parser.Term.dbgTrace| dbg_trace%$dbgTraceTk $arg ;%$semicolonTk $body:term) => do
    let components := #[dbgTraceTk, arg]
    let instruction := Layouts.pseudoApplication (← components.mapM fmt)
    fmtTermInstruction instruction components semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.idbg]
public def fmtIdbg : Fmt := fun
  | `(Parser.Term.idbg| idbg%$idbgTk $t:term ;%$semicolonTk $body:term) => do
    let components := #[idbgTk, t]
    let instruction := Layouts.pseudoApplication (← components.mapM fmt)
    fmtTermInstruction instruction components semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.assert]
public def fmtAssert : Fmt := fun
  | `(Parser.Term.assert| assert!%$assertTk $cond:term ;%$semicolonTk $body:term) => do
    let components := #[assertTk, cond]
    let instruction := Layouts.pseudoApplication (← components.mapM fmt)
    fmtTermInstruction instruction components semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.debugAssert]
public def fmtDebugAssert : Fmt := fun
  | `(Parser.Term.debugAssert| debug_assert!%$debugAssertTk $cond:term ;%$semicolonTk $body:term) =>
    do
      let components := #[debugAssertTk, cond]
      let instruction := Layouts.pseudoApplication (← components.mapM fmt)
      fmtTermInstruction instruction components semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.clear]
public def fmtClear : Fmt := fun
  | `(Parser.Term.clear| clear%%$clearTk $id:ident ;%$semicolonTk $body:term) => do
    let components := #[clearTk, id]
    let instruction := Layouts.pseudoApplication (← components.mapM fmt)
    fmtTermInstruction instruction components semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.nomatch]
public def fmtNomatch : Fmt := fun
  | `(Parser.Term.nomatch| nomatch%$nomatchTk $terms:term,*) => do
    let nomatchTk ← fmt nomatchTk
    let terms ← fmtTSepArray terms
    return Layouts.keywordPrefixedSepFill nomatchTk terms .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.stateRefT]
public def fmtStateRefT : Fmt := fun
  | `(Parser.Term.stateRefT| StateRefT%$stateRefTTk $arg:term $last) => do
    if last.raw.getKind == ``Parser.Term.macroDollarArg then
      let lhs ← fmtAppLike #[stateRefTTk, arg]
      let dollarTk ← fmt (← getStxArg! last 0)
      let rhs ← fmt (← getStxArg! last 1)
      return Layouts.pipeOperator #[lhs, dollarTk, rhs]
    else
      fmtAppLike #[stateRefTTk, arg, last]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letMVar]
public def fmtLetMVar : Fmt := fun
  | `(Parser.Term.letMVar|
      let_mvar%%$letMVarTk ?%$questionTk $id:ident :=%$colonEqTk $value:term ;%$semicolonTk $body:term) =>
    do
      let components := #[letMVarTk, questionTk, id, colonEqTk, value]
      let letMVarTk ← fmt letMVarTk
      let questionTk ← fmt questionTk
      let id ← fmt id
      let lhs := Layouts.atomic #[questionTk, id]
      let colonEqTk ← fmt colonEqTk
      let value ← fmt value
      let decl := Layouts.assignmentDeclaration lhs colonEqTk value
      let fullDecl := Layouts.letDecl letMVarTk empty decl
      fmtTermInstruction fullDecl components semicolonTk body
  | _ =>
    throw .partialFormatter

public def fmtWaitIfMVarLike (kwTk questionTk id semicolonTk body : Syntax) : FmtM TaggedDoc := do
  let components := #[kwTk, questionTk, id]
  let kwTk ← fmt kwTk
  let questionTk ← fmt questionTk
  let id ← fmt id
  let lhs := Layouts.atomic #[questionTk, id]
  let instruction := Layouts.pseudoApplication #[kwTk, lhs]
  fmtTermInstruction instruction components semicolonTk body

@[builtin_fmt Lean.Parser.Term.waitIfTypeMVar]
public def fmtWaitIfTypeMVar : Fmt := fun
  | `(Parser.Term.waitIfTypeMVar|
      wait_if_type_mvar%%$kwTk ?%$questionTk $id:ident ;%$semicolonTk $body:term) =>
    fmtWaitIfMVarLike kwTk questionTk id semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.waitIfTypeContainsMVar]
public def fmtWaitIfTypeContainsMVar : Fmt := fun
  | `(Parser.Term.waitIfTypeContainsMVar|
      wait_if_type_contains_mvar%%$kwTk ?%$questionTk $id:ident ;%$semicolonTk $body:term) =>
    fmtWaitIfMVarLike kwTk questionTk id semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.waitIfContainsMVar]
public def fmtWaitIfContainsMVar : Fmt := fun
  | `(Parser.Term.waitIfContainsMVar|
      wait_if_contains_mvar%%$kwTk ?%$questionTk $id:ident ;%$semicolonTk $body:term) =>
    fmtWaitIfMVarLike kwTk questionTk id semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.waitForExpectedType]
public def fmtWaitForExpectedType : Fmt := fun
  | `(Parser.Term.waitForExpectedType|
      wait_for_expected_type%$kwTk $t:term) => do
    fmtAppLike #[kwTk, t]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.withDeclName]
public def fmtWithDeclName : Fmt := fun
  | `(Parser.Term.withDeclName| with_decl_name%%$withDeclNameTk $[?%$questionTk?]? $id:ident $e:term) =>
    do
      let withDeclNameTk ← fmt withDeclNameTk
      let questionTk? ← fmt? questionTk?
      let id ← fmt id
      let e ← fmt e
      let lhs := Layouts.atomic #[questionTk?, id]
      return Layouts.application #[withDeclNameTk, lhs, e]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.dynamicQuot]
public def fmtDynamicQuot : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Tactic.quot]
public def fmtTacticQuot : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Tactic.quotSeq]
public def fmtTacticQuotSeq : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Term.leading_parser]
public def fmtLeadingParser : Fmt := fun
  | `(Parser.Term.leading_parser|
      leading_parser%$leadingParserTk $[:%$colonTk? $prec?:term]? $[$anon?:withAnonymousAntiquot]? $body:term) =>
    do
      let leadingParserTk ← fmt leadingParserTk
      let colonTk? ← fmt? colonTk?
      let prec? ← fmt? prec?
      let anon? ← fmt? anon?
      let body ← fmt body
      let withPrec := nested <| Layouts.atomic #[leadingParserTk, colonTk?, prec?]
      let lhs := Layouts.pseudoApplication #[withPrec, anon?]
      return Layouts.application #[lhs, body]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.trailing_parser]
public def fmtTrailingParser : Fmt := fun
  | `(Parser.Term.trailing_parser|
      trailing_parser%$trailingParserTk $[:%$colon1Tk? $prec1?:term]? $[:%$colon2Tk? $prec2?:term]? $body:term) =>
    do
      let trailingParserTk ← fmt trailingParserTk
      let colon1Tk? ← fmt? colon1Tk?
      let prec1? ← fmt? prec1?
      let colon2Tk? ← fmt? colon2Tk?
      let prec2? ← fmt? prec2?
      let body ← fmt body
      let withPrecs :=
        nested <| Layouts.atomic #[trailingParserTk, colon1Tk?, prec1?, colon2Tk?, prec2?]
      return Layouts.application #[withPrecs, body]
  | _ =>
    throw .partialFormatter

public def fmtOptConfig (stx : TSyntax ``Parser.Term.optConfig) : FmtM (Array TaggedDoc) := do
  match stx with
  | `(Parser.Term.optConfig| $items:configItem*) => fmtArray items
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.configItem]
public def fmtConfigItem : Fmt := fun
  | `(Parser.Term.configItem| $item:posConfigItem) => fmt item
  | `(Parser.Term.configItem| $item:negConfigItem) => fmt item
  | `(Parser.Term.configItem| $item:valConfigItem) => fmt item
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.posConfigItem]
public def fmtPosConfigItem : Fmt := fun
  | `(Parser.Term.posConfigItem| +%$plusTk$id:ident) => do
    let plusTk ← fmt plusTk
    let id ← fmt id
    return Layouts.prefixOperator plusTk id .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.negConfigItem]
public def fmtNegConfigItem : Fmt := fun
  | `(Parser.Term.negConfigItem| -%$minusTk$id:ident) => do
    let minusTk ← fmt minusTk
    let id ← fmt id
    return Layouts.prefixOperator minusTk id .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.valConfigItem]
public def fmtValConfigItem : Fmt := fun
  | `(Parser.Term.valConfigItem| (%$lbTk $id:ident :=%$colonEqTk $body:term )%$rbTk) =>
    fmtNamedArgumentTerm lbTk id colonEqTk body rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.withAnonymousAntiquot]
public def fmtWithAnonymousAntiquot : Fmt := fun
  | `(Parser.Term.withAnonymousAntiquot| (%$lbTk withAnonymousAntiquot%$kwTk :=%$colonEqTk $flag )%$rbTk) =>
    fmtNamedArgumentTerm lbTk kwTk colonEqTk flag rbTk
  | _ =>
    throw .partialFormatter

public def fmtSufficesDecl
    (sufficesTk : Syntax) (id? colonTk? : Option Syntax) (goal kwTk rhs : Syntax)
    : FmtM TaggedDoc := do
  let sufficesTk ← fmt sufficesTk
  let id? ← fmt? id?
  let colonTk? ← fmt? colonTk?
  let goal ← fmt goal
  let kwTk ← fmt kwTk
  let rhs ← fmt rhs
  let idGoal := Layouts.typeAscription id? colonTk? goal
  let lhs := Layouts.pseudoApplication #[sufficesTk, idGoal]
  return Layouts.keywordSeparated lhs kwTk rhs

public def fmtSufficesFrom
    (sufficesTk : Syntax) (id? colonTk? : Option Syntax)
    (goal fromTk proof semicolonTk body : Syntax)
    : FmtM TaggedDoc := do
  let decl ← fmtSufficesDecl sufficesTk id? colonTk? goal fromTk proof
  fmtTermInstruction decl
    (#[sufficesTk] ++ id?.toArray ++ colonTk?.toArray ++ #[goal, fromTk, proof]) semicolonTk body

public def fmtSufficesBy
    (sufficesTk : Syntax) (id? colonTk? : Option Syntax) (goal byTk tac semicolonTk body : Syntax)
    : FmtM TaggedDoc := do
  let decl ← fmtSufficesDecl sufficesTk id? colonTk? goal byTk tac
  fmtTermInstruction decl (#[sufficesTk] ++ id?.toArray ++ colonTk?.toArray ++ #[goal, byTk, tac])
    semicolonTk body

@[builtin_fmt Lean.Parser.Term.suffices]
public def fmtSuffices : Fmt := fun
  | `(Parser.Term.suffices|
      suffices%$sufficesTk $x:ident :%$colonTk $goal:term from%$fromTk $proof:term ;%$semicolonTk $body:term) =>
    fmtSufficesFrom sufficesTk x colonTk goal fromTk proof semicolonTk body
  | `(Parser.Term.suffices|
      suffices%$sufficesTk _%$x :%$colonTk $goal:term from%$fromTk $proof:term ;%$semicolonTk $body:term) =>
    fmtSufficesFrom sufficesTk x colonTk goal fromTk proof semicolonTk body
  | `(Parser.Term.suffices|
      suffices%$sufficesTk $_:hygieneInfo $goal:term from%$fromTk $proof:term ;%$semicolonTk $body:term) =>
    fmtSufficesFrom sufficesTk none none goal fromTk proof semicolonTk body
  | `(Parser.Term.suffices|
      suffices%$sufficesTk $x:ident :%$colonTk $goal:term by%$byTk $tac:tacticSeq ;%$semicolonTk $body:term) =>
    fmtSufficesBy sufficesTk x colonTk goal byTk tac semicolonTk body
  | `(Parser.Term.suffices|
      suffices%$sufficesTk _%$x :%$colonTk $goal:term by%$byTk $tac:tacticSeq ;%$semicolonTk $body:term) =>
    fmtSufficesBy sufficesTk x colonTk goal byTk tac semicolonTk body
  | `(Parser.Term.suffices|
      suffices%$sufficesTk $_:hygieneInfo $goal:term by%$byTk $tac:tacticSeq ;%$semicolonTk $body:term) =>
    fmtSufficesBy sufficesTk none none goal byTk tac semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.haveI]
public def fmtHaveI : Fmt := fun
  | `(Parser.Term.haveI| haveI%$haveITk $config:letConfig $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm haveITk config decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letI]
public def fmtLetI : Fmt := fun
  | `(Parser.Term.letI| letI%$letITk $config:letConfig $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm letITk config decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.let_fun]
public def fmtLetFun : Fmt := fun
  | `(Parser.Term.let_fun| let_fun%$letFunTk $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm letFunTk none decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.let_delayed]
public def fmtLetDelayed : Fmt := fun
  | `(Parser.Term.let_delayed| let_delayed%$letDelayedTk $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm letDelayedTk none decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.let_tmp]
public def fmtLetTmp : Fmt := fun
  | `(Parser.Term.let_tmp| let_tmp%$letTmpTk $decl:letDecl ;%$semicolonTk $body:term) =>
    fmtLetTerm letTmpTk none decl semicolonTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.matchExprPat]
public def fmtMatchExprPat : Fmt := fun
  | `(Parser.Term.matchExprPat| $[$id?:ident @%$atTk?]? $f:ident $binderIdents*) => do
    let f ← fmt f
    let binderIdents ← fmtArray binderIdents
    let rhs := Layouts.pseudoApplication <| #[f] ++ binderIdents
    let id? ← fmt? id?
    let atTk? ← fmt? atTk?
    return Layouts.atomic #[id?, atTk?, rhs]
  | _ =>
    throw .partialFormatter

public def fmtMatchExprAlt : Syntax → FmtM Layouts.Types.Alt := fun
  | `(Parser.Term.matchExprAltExpr| |%$pipeTk $pat:matchExprPat =>%$arrowTk $rhs:term) => do
    let pipeTk ← fmt pipeTk
    let pat ← fmt pat
    let arrowTk ← fmt arrowTk
    let rhs ← fmt rhs
    let lhs := nested <| Layouts.spacedAtomic #[pipeTk, pat]
    return Layouts.alt #[lhs] arrowTk rhs
  | _ =>
    throw .partialFormatter

meta def matchExprElseAltF := Parser.Term.matchExprElseAlt Parser.termParser

public def fmtMatchExprElseAlt : Syntax → FmtM Layouts.Types.Alt := fun
  | `(matchExprElseAltF| |%$pipeTk $h:hole =>%$arrowTk $rhs:term) => do
    let pipeTk ← fmt pipeTk
    let h ← fmt h
    let arrowTk ← fmt arrowTk
    let rhs ← fmt rhs
    let lhs := nested <| Layouts.spacedAtomic #[pipeTk, h]
    return Layouts.alt #[lhs] arrowTk rhs
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.matchExprAlts]
public def fmtMatchExprAlts : Fmt := fun stx => do
  if stx.getKind != ``Parser.Term.matchExprAlts then
    throw .partialFormatter
  let alts ← (← getStxArg! stx 0).getArgs.mapM fmtMatchExprAlt
  let elseAlt ← fmtMatchExprElseAlt (← getStxArg! stx 1)
  let alts := alts.push elseAlt
  return Layouts.alts alts

@[builtin_fmt Lean.Parser.Term.matchExpr]
public def fmtMatchExpr : Fmt := fun
  | `(Parser.Term.matchExpr| match_expr%$matchExprTk $discr:term with%$withTk $alts:matchExprAlts) =>
    do
      let matchExprTk ← fmt matchExprTk
      let discr ← fmt discr
      let lhs := Layouts.pseudoApplication #[matchExprTk, discr]
      let withTk ← fmt withTk
      let alts ← fmt alts
      return Layouts.keywordSeparated lhs withTk alts {
        allowFlattening := false
        nestedRhs := false
      }
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Term.letExpr]
public def fmtLetExpr : Fmt := fun
  | `(Parser.Term.letExpr|
      let_expr%$letExprTk $pat:matchExprPat :=%$colonEqTk $value:term |%$pipeTk $alt:term ;%$semicolonTk $body:term) =>
    do
      let components := #[letExprTk, pat, colonEqTk, value, pipeTk, alt]
      let letExprTk ← fmt letExprTk
      let pat ← fmt pat
      let colonEqTk ← fmt colonEqTk
      let value ← fmt value
      let pipeTk ← fmt pipeTk
      let alt ← fmt alt
      let assignment := Layouts.assignmentDeclaration pat colonEqTk value
      let pipeAlt := nested <| Layouts.softSpacedAtomic #[pipeTk, alt]
      let decl := Layouts.matchDeclaration assignment pipeAlt
      let fullDecl := Layouts.letDecl letExprTk empty decl
      fmtTermInstruction fullDecl components semicolonTk body
  | _ =>
    throw .partialFormatter
