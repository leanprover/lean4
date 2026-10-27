/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Syntax
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

public def metaDeclarationSignature
    (declTk : TaggedDoc) (declSuffix? : TaggedDoc) (declParams : Array TaggedDoc)
    (metaSignature? : TaggedDoc) (colonTk? : TaggedDoc) (kind? : TaggedDoc) :=
  let fullDeclTk :=
    Layouts.pseudoApplication <|
      #[Layouts.prefixOperator declTk declSuffix? .withoutSpacing] ++ declParams
  let lhs := Layouts.horizontalOrVertical #[fullDeclTk, metaSignature?]
  hardNested <| Layouts.horizontalOrVertical #[
    lhs,
    Layouts.prefixOperator colonTk? kind? .withSpacing
  ]

public def fmtMetaDeclarationSignature
    (declTk : Syntax) (declSuffix? : Option Syntax) (declParams : Array TaggedDoc)
    (metaSignature? : TaggedDoc) (colonTk? : Option Syntax) (kind? : Option Syntax)
    : FmtM TaggedDoc := do
  let declTk ← fmt declTk
  let declSuffix? ← fmt? declSuffix?
  let colonTk? ← fmt? colonTk?
  let kind? ← fmt? kind?
  return metaDeclarationSignature declTk declSuffix? declParams metaSignature? colonTk? kind?

public def fmtElabDeclarationSignature
    (declTk : Syntax) (declSuffix? : Option Syntax) (declParams : Array TaggedDoc)
    (metaSignature : TaggedDoc) (colonTk? : Option Syntax) (kind? : Option Syntax)
    (leTk? : Option Syntax) (expectedType? : Option Syntax)
    : FmtM TaggedDoc := do
  let declTk ← fmt declTk
  let declSuffix? ← fmt? declSuffix?
  let colonTk? ← fmt? colonTk?
  let kind? ← fmt? kind?
  let leTk? ← fmt? leTk?
  let expectedType? ← fmt? expectedType?
  let fullDeclTk :=
    Layouts.pseudoApplication <|
      #[Layouts.prefixOperator declTk declSuffix? .withoutSpacing] ++ declParams
  let lhs := Layouts.horizontalOrVertical #[fullDeclTk, metaSignature]
  return Layouts.infixOperator #[lhs, colonTk?, kind?, leTk?, expectedType?]

public def fmtMetaAssignmentDeclaration
    (docComment? : Option (TSyntax ``Parser.Command.docComment))
    (attributes? : Option (TSyntax ``Parser.Term.attributes)) (mods : Array (Option Syntax))
    (declTk : Syntax) (declSuffix? : Option Syntax) (declParams : Array TaggedDoc)
    (metaSignature : TaggedDoc) (colonTk? : Option Syntax) (kind? : Option Syntax) (sepTk : Syntax)
    (body : Syntax) (rawBody : Bool)
    : FmtM TaggedDoc := do
  let signature ←
    fmtMetaDeclarationSignature declTk declSuffix? declParams metaSignature colonTk? kind?
  let sepTk ← fmt sepTk
  let body ←
    if rawBody then
      fmtRaw (isFallback := false) body
    else
      fmt body
  let decl := Layouts.assignmentDeclaration signature sepTk body
  fmtDeclWithModifiers docComment? attributes? mods decl

public def fmtMetaMatchDeclaration
    (docComment? : Option (TSyntax ``Parser.Command.docComment))
    (attributes? : Option (TSyntax ``Parser.Term.attributes)) (mods : Array (Option Syntax))
    (declTk : Syntax) (declSuffix? : Option Syntax) (declParams : Array TaggedDoc)
    (metaSignature : TaggedDoc) (colonTk? : Option Syntax) (kind? : Option Syntax)
    (matchAlts : TSyntax ``Parser.Term.matchAlts)
    : FmtM TaggedDoc := do
  let signature ←
    fmtMetaDeclarationSignature declTk declSuffix? declParams metaSignature colonTk? kind?
  let matchAlts ← fmt matchAlts
  let decl := Layouts.matchDeclaration signature matchAlts
  fmtDeclWithModifiers docComment? attributes? mods decl

@[builtin_fmt Lean.Parser.precedence]
public def fmtPrecedence : Fmt := fun
  | `(Parser.precedence| :%$colonTk $prec:prec) => do
    let colonTk ← fmt colonTk
    let prec ← fmt prec
    return Layouts.prefixOperator colonTk prec .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.paren]
public def fmtSyntaxParen : Fmt := fun
  | `(Parser.Syntax.paren| (%$lbTk $[$args:stx]* )%$rbTk) => do
    let lbTk ← fmt lbTk
    let mut args ← fmtArray args
    let rbTk ← fmt rbTk
    if args.size > 1 then
      args := args.modify 0 hardNested
    let args' := Layouts.fill args
    return Layouts.parens lbTk args' rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.cat]
public def fmtSyntaxCat : Fmt := fun
  | `(Parser.Syntax.cat| $catId:ident $[$prec?:precedence]?) => do
    let catId ← fmt catId
    let prec? ← fmt? prec?
    return Layouts.prefixOperator catId prec? .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.unary]
public def fmtSyntaxUnary : Fmt := fun
  | `(Parser.Syntax.unary| $parserId:ident(%$lbTk $[$args]* )%$rbTk) => do
    let parserId ← fmt parserId
    let lbTk ← fmt lbTk
    let args ← fmtArray args
    let rbTk ← fmt rbTk
    let lb := Layouts.atomic #[parserId, lbTk]
    return Layouts.metaApplication lb #[.elems args] rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.binary]
public def fmtSyntaxBinary : Fmt := fun
  | `(Parser.Syntax.binary| $parserId:ident(%$lbTk $[$args₁]* ,%$commaTk $[$args₂]* )%$rbTk) => do
    let parserId ← fmt parserId
    let lbTk ← fmt lbTk
    let args₁ ← fmtArray args₁
    let commaTk ← fmt commaTk
    let args₂ ← fmtArray args₂
    let rbTk ← fmt rbTk
    let lb := Layouts.atomic #[parserId, lbTk]
    let terms := #[.elems args₁, .sep commaTk, .elems args₂]
    return Layouts.metaApplication lb terms rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.sepBy]
public def fmtSyntaxSepBy : Fmt := fun
  | `(Parser.Syntax.sepBy|
      sepBy(%$lbTk $[$args]* ,%$comma₁Tk $sepStr:str
        $[,%$comma₂Tk? $[$sepParserArgs?]*]? $[,%$comma₃Tk? allowTrailingSep%$allowTrailingSepTk?]? )%$rbTk) =>
    do
      let lbTk ← fmt lbTk
      let args ← fmtArray args
      let comma₁Tk ← fmt comma₁Tk
      let sepStr ← fmt sepStr
      let comma₂Tk? ← fmt? comma₂Tk?
      let sepParserArgs ← fmtArray <| sepParserArgs?.getD #[]
      let comma₃Tk? ← fmt? comma₃Tk?
      let allowTrailingSepTk? ← fmt? allowTrailingSepTk?
      let rbTk ← fmt rbTk
      let terms := #[
        .elems args,
        .sep comma₁Tk,
        .elems #[sepStr],
        .sep comma₂Tk?,
        .elems sepParserArgs,
        .sep comma₃Tk?,
        .elems #[allowTrailingSepTk?]
      ]
      return Layouts.metaApplication lbTk terms rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.sepBy1]
public def fmtSyntaxSepBy1 : Fmt := fun
  | `(Parser.Syntax.sepBy1|
      sepBy1(%$lbTk $[$args]* ,%$comma₁Tk $sepStr:str
        $[,%$comma₂Tk? $[$sepParserArgs?]*]? $[,%$comma₃Tk? allowTrailingSep%$allowTrailingSepTk?]? )%$rbTk) =>
    do
      let lbTk ← fmt lbTk
      let args ← fmtArray args
      let comma₁Tk ← fmt comma₁Tk
      let sepStr ← fmt sepStr
      let comma₂Tk? ← fmt? comma₂Tk?
      let sepParserArgs ← fmtArray <| sepParserArgs?.getD #[]
      let comma₃Tk? ← fmt? comma₃Tk?
      let allowTrailingSepTk? ← fmt? allowTrailingSepTk?
      let terms := #[
        .elems args,
        .sep comma₁Tk,
        .elems #[sepStr],
        .sep comma₂Tk?,
        .elems sepParserArgs,
        .sep comma₃Tk?,
        .elems #[allowTrailingSepTk?]
      ]
      let rbTk ← fmt rbTk
      return Layouts.metaApplication lbTk terms rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.atom]
public def fmtSyntaxAtom : Fmt := fun
  | `(Parser.Syntax.atom| $atomStr:str) => fmt atomStr
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.nonReserved]
public def fmtSyntaxNonReserved : Fmt := fun
  | `(Parser.Syntax.nonReserved| &%$ampTk $atomStr:str) => do
    let ampTk ← fmt ampTk
    let atomStr ← fmt atomStr
    return Layouts.atomic #[ampTk, atomStr]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Syntax.unicodeAtom]
public def fmtSyntaxUnicodeAtom : Fmt := fun
  | `(Parser.Syntax.unicodeAtom|
      unicode(%$lbTk $unicodeStr:str ,%$comma₁Tk $asciiStr:str
        $[,%$comma₂Tk? preserveForPP%$preserveForPPTk?]? )%$rbTk) => do
    let lbTk ← fmt lbTk
    let unicodeStr ← fmt unicodeStr
    let comma₁Tk ← fmt comma₁Tk
    let asciiStr ← fmt asciiStr
    let comma₂Tk? ← fmt? comma₂Tk?
    let preserveForPPTk? ← fmt? preserveForPPTk?
    let terms := #[
      .elems #[unicodeStr], .sep comma₁Tk, .elems #[asciiStr], .sep comma₂Tk?,
      .elems #[preserveForPPTk?]
    ]
    let rbTk ← fmt rbTk
    return Layouts.metaApplication lbTk terms rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.namedName]
public def fmtNamedName : Fmt := fun
  | `(Parser.Command.namedName| (%$lbTk name%$nameTk :=%$colonEqTk $name:ident )%$rbTk) =>
    fmtNamedArgumentTerm lbTk nameTk colonEqTk name rbTk
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.identPrec]
public def fmtIdentPrec : Fmt := fun
  | `(Parser.Command.identPrec| $id:ident $[$prec?:precedence]?) => do
    let id ← fmt id
    let prec? ← fmt? prec?
    return Layouts.prefixOperator id prec? .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.prefix]
public def fmtPrefix : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.infix]
public def fmtInfix : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.infixl]
public def fmtInfixl : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.infixr]
public def fmtInfixr : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.postfix]
public def fmtPostfix : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.mixfix]
public def fmtMixfix : Fmt := fun
  | `(Parser.Command.mixfix|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind $mixfixKind $prec:precedence
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $item:notationItem =>%$darrowTk
        $rhs:term) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let item ← fmt item
    let metaSignature := Layouts.fill #[item]
    -- Mixfix bodies are elaborated as quotations, so we format them as such
    fmtMetaAssignmentDeclaration docComment? attributes? #[attrKind] mixfixKind prec
      #[namedName?, namedPrio?] metaSignature none none darrowTk rhs (rawBody := true)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.notation]
public def fmtNotation : Fmt := fun
  | `(Parser.Command.«notation»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind notation%$notationTk $[$prec?:precedence]?
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $[$items]* =>%$darrowTk
        $rhs:term) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let items ← fmtArray items
    let metaSignature := Layouts.fill items
    -- Notation bodies are elaborated as quotations, so we format them as such
    fmtMetaAssignmentDeclaration docComment? attributes? #[attrKind] notationTk prec?
      #[namedName?, namedPrio?] metaSignature none none darrowTk rhs (rawBody := true)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.macro_rules]
public def fmtMacroRules : Fmt := fun
  | `(Parser.Command.«macro_rules»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind macro_rules%$macroRulesTk
          $[(%$lbTk? kind%$kindTk? :=%$colonEqTk? $kindId?:ident )%$rbTk?]?
        $alts:matchAlts) => do
    let kindParam? ← fmtNamedArgumentTerm? lbTk? kindTk? colonEqTk? kindId? rbTk?
    fmtMetaMatchDeclaration docComment? attributes? #[attrKind] macroRulesTk none #[kindParam?]
      empty none none alts
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.syntax]
public def fmtSyntaxCmd : Fmt := fun
  | `(Parser.Command.«syntax»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind syntax%$syntaxTk $[$prec?:precedence]?
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $[$args]*
          :%$colonTk $cat:ident) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let args ← fmtArray args
    let metaSignature := Layouts.fill args
    let signature ←
      fmtMetaDeclarationSignature syntaxTk prec? #[namedName?, namedPrio?] metaSignature colonTk cat
    fmtDeclWithModifiers docComment? attributes? #[attrKind] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.syntaxAbbrev]
public def fmtSyntaxAbbrev : Fmt := fun
  | `(Parser.Command.syntaxAbbrev|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      syntax%$syntaxTk $id:ident :=%$colonEqTk $[$args:stx]*) => do
    let syntaxTk ← fmt syntaxTk
    let id ← fmt id
    let signature := Layouts.pseudoApplication #[syntaxTk, id]
    let colonEqTk ← fmt colonEqTk
    let args ← fmtArray args
    let body := withPosition <| Layouts.fill args
    let decl := Layouts.assignmentDeclaration signature colonEqTk body
    fmtDeclWithModifiers docComment? none #[visibility?] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.catBehaviorBoth]
public def fmtCatBehaviorBoth : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.catBehaviorSymbol]
public def fmtCatBehaviorSymbol : Fmt := fmtAtomic

@[builtin_fmt Lean.Parser.Command.syntaxCat]
public def fmtDeclareSyntaxCat : Fmt := fun
  | `(Parser.Command.syntaxCat|
      $[$docComment?:docComment]?
      declare_syntax_cat%$declareSyntaxCatTk $catId:ident
        $[(%$lbTk? behavior%$behaviorTk? :=%$colonEqTk? $behavior? )%$rbTk?]?) => do
    let docComment? ← fmt? docComment?
    let declareSyntaxCatTk ← fmt declareSyntaxCatTk
    let catId ← fmt catId
    let behaviorParam? ← fmtNamedArgumentTerm? lbTk? behaviorTk? colonEqTk? behavior? rbTk?
    let decl := Layouts.pseudoApplication #[declareSyntaxCatTk, catId, behaviorParam?]
    return Layouts.lines #[docComment?, decl]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.macroArg]
public def fmtMacroArg : Fmt := fun
  | `(Parser.Command.macroArg| $[$id?:ident:%$colonTk?]? $arg:stx) => do
    let id? ← fmt? id?
    let colonTk? ← fmt? colonTk?
    let arg ← fmt arg
    return Layouts.atomicInfixOperator #[id?, colonTk?, arg]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.macroRhs]
public def fmtMacroRhs : Fmt := fun
  | `(Parser.Command.macroRhs| $rhs:term) => do
    let rhs ← fmt rhs
    return withPosition rhs
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.macro]
public def fmtMacro : Fmt := fun
  | `(Parser.Command.«macro»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind macro%$macroTk $[$prec?:precedence]?
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $[$args:macroArg]*
          :%$colonTk $cat:ident =>%$darrowTk
        $rhs:macroRhs) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let args ← fmtArray args
    let metaSignature := Layouts.fill args
    fmtMetaAssignmentDeclaration docComment? attributes? #[attrKind] macroTk prec?
      #[namedName?, namedPrio?] metaSignature colonTk cat darrowTk rhs (rawBody := false)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.elab_rules]
public def fmtElabRules : Fmt := fun
  | `(Parser.Command.«elab_rules»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind elab_rules%$elabRulesTk
          $[(%$lbTk? kind%$kindTk? :=%$colonEqTk? $kindId?:ident )%$rbTk?]?
          $[:%$catColonTk? $cat?:ident]? $[<=%$leTk? $expectedType?:ident]?
        $alts:matchAlts) => do
    let kindParam? ← fmtNamedArgumentTerm? lbTk? kindTk? colonEqTk? kindId? rbTk?
    let signature ←
      fmtElabDeclarationSignature elabRulesTk none #[kindParam?] empty catColonTk? cat? leTk?
        expectedType?
    let alts ← fmt alts
    let decl := Layouts.matchDeclaration signature alts
    fmtDeclWithModifiers docComment? attributes? #[attrKind] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.elab]
public def fmtElab : Fmt := fun
  | `(Parser.Command.«elab»|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $attrKind:attrKind elab%$elabTk $[$prec?:precedence]?
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $[$args:macroArg]*
          :%$colonTk $cat:ident $[<=%$leTk? $expectedType?:ident]? =>%$darrowTk
        $rhs:term) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let args ← fmtArray args
    let darrowTk ← fmt darrowTk
    let rhs ← fmt rhs
    let metaSignature := Layouts.fill args
    let signature ←
      fmtElabDeclarationSignature elabTk prec? #[namedName?, namedPrio?] metaSignature colonTk cat
        leTk? expectedType?
    let decl := Layouts.assignmentDeclaration signature darrowTk rhs
    fmtDeclWithModifiers docComment? attributes? #[attrKind] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Command.binderPredicate]
public def fmtBinderPredicate : Fmt := fun
  | `(Parser.Command.binderPredicate|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $[$attrKind?:attrKind]? binder_predicate%$binderPredicateTk
          $[$namedName?:namedName]? $[$namedPrio?:namedPrio]?
          $binderId:ident $[$args:macroArg]* =>%$darrowTk
        $rhs:term) => do
    let namedName? ← fmt? namedName?
    let namedPrio? ← fmt? namedPrio?
    let binderId ← fmt binderId
    let args ← fmtArray args
    let metaSignature := Layouts.fill <| #[binderId] ++ args
    fmtMetaAssignmentDeclaration docComment? attributes? #[attrKind?] binderPredicateTk none
      #[namedName?, namedPrio?] metaSignature none none darrowTk rhs (rawBody := false)
  | _ =>
    throw .partialFormatter
