/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lake.Formatters.DSL.DeclUtil
public import Lake.DSL.Syntax
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt Lake.DSL

namespace Lake.Formatters

@[builtin_fmt Lake.DSL.getConfig]
public def fmtGetConfig : Fmt := fun
  | `(getConfig| get_config?%$getConfigTk $id:ident) => fmtAppLike #[getConfigTk, id]
  | _ => throw .partialFormatter

/--
Formats the `<keyword> <name>` head of a Lake configuration declaration together with its
declarative configuration.
-/
def fmtConfigCommand (kwTk : Syntax) (name? : Option IdentOrStr) (config : OptConfig)
    : FmtM TaggedDoc := do
  let kwTk ← fmt kwTk
  let name? ← fmt? name?
  let signature := Layouts.pseudoApplication #[kwTk, name?]
  fmtWithOptConfig signature config

@[builtin_fmt Lake.DSL.packageCommand]
public def fmtPackageCommand : Fmt := fun
  | `(packageCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? package%$packageTk
        $[$name?:identOrStr]? $config:optConfig) => do
    let decl ← fmtConfigCommand packageTk name? config
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.leanLibCommand]
public def fmtLeanLibCommand : Fmt := fun
  | `(leanLibCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? lean_lib%$leanLibTk
        $[$name?:identOrStr]? $config:optConfig) => do
    let decl ← fmtConfigCommand leanLibTk name? config
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.leanExeCommand]
public def fmtLeanExeCommand : Fmt := fun
  | `(leanExeCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? lean_exe%$leanExeTk
        $[$name?:identOrStr]? $config:optConfig) => do
    let decl ← fmtConfigCommand leanExeTk name? config
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.inputFileCommand]
public def fmtInputFileCommand : Fmt := fun
  | `(inputFileCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? input_file%$inputFileTk
        $[$name?:identOrStr]? $config:optConfig) => do
    let decl ← fmtConfigCommand inputFileTk name? config
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.inputDirCommand]
public def fmtInputDirCommand : Fmt := fun
  | `(inputDirCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? input_dir%$inputDirTk
        $[$name?:identOrStr]? $config:optConfig) => do
    let decl ← fmtConfigCommand inputDirTk name? config
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

/-- The termination suffix of Lake declaration bodies, which never carry termination hints. -/
def emptyTerminationSuffix : TSyntax ``Parser.Termination.suffix :=
  Unhygienic.run `(Parser.Termination.suffix|)

@[builtin_fmt Lake.DSL.postUpdateDecl]
public def fmtPostUpdateDecl : Fmt := fun
  | `(postUpdateDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? post_update%$postUpdateTk
        $[$binder?:simpleBinder]? :=%$colonEqTk $declBody:term $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    let decl ←
      fmtAssignmentDeclaration postUpdateTk none binder? #[] none none colonEqTk declBody
        terminationSuffix whereDecls?
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | `(postUpdateDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? post_update%$postUpdateTk
        $[$binder?:simpleBinder]? $declBody:do $[$whereDecls?:whereDecls]?) => do
    let decl ←
      fmtAssignmentDeclaration postUpdateTk none binder? #[] none none none declBody
        emptyTerminationSuffix whereDecls?
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.fromPath]
public def fmtFromPath : Fmt := fun
  | `(fromPath| $path:term) => fmt path
  | _ => throw .partialFormatter

@[builtin_fmt Lake.DSL.fromGit]
public def fmtFromGit : Fmt := fun
  | `(fromGit| git%$gitTk $url:term $[@%$atTk? $rev?:term]? $[/%$slashTk? $subDir?:term]?) => do
    let gitTk ← fmt gitTk
    let url ← fmt url
    let atTk? ← fmt? atTk?
    let rev? ← fmt? rev?
    let slashTk? ← fmt? slashTk?
    let subDir? ← fmt? subDir?
    let repository := Layouts.infixOperator #[url, atTk?, rev?] .dense
    let source := Layouts.infixOperator #[repository, slashTk?, subDir?] .dense
    return Layouts.keywordPrefixedTerm gitTk source .sticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.fromSource]
public def fmtFromSource : Fmt := fun
  | `(fromSource| $git:fromGit) => fmt git
  | `(fromSource| $path:fromPath) => fmt path
  | _ => throw .partialFormatter

@[builtin_fmt Lake.DSL.fromClause]
public def fmtFromClause : Fmt := fun
  | `(fromClause| from%$fromTk $source:fromSource) => do
    let fromTk ← fmt fromTk
    let source ← fmt source
    return Layouts.keywordPrefixedTerm fromTk source .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.withClause]
public def fmtWithClause : Fmt := fun
  | `(withClause| with%$withTk $opts:term) => do
    let withTk ← fmt withTk
    let opts ← fmt opts
    return Layouts.keywordPrefixedTerm withTk opts .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.depName]
public def fmtDepName : Fmt := fun
  | `(depName| $[$scope?:str /%$slashTk?]? $name:identOrStr) => do
    let scope? ← fmt? scope?
    let slashTk? ← fmt? slashTk?
    let name ← fmt name
    return Layouts.infixOperator #[scope?, slashTk?, name] .dense
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.verSpec]
public def fmtVerSpec : Fmt := fun
  | `(verSpec| $[git%$gitTk?]? $ver:term) => do
    let gitTk? ← fmt? gitTk?
    let ver ← fmt ver
    return Layouts.keywordPrefixedTerm gitTk? ver .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.requireDecl]
public def fmtRequireDecl : Fmt := fun
  | `(requireDecl|
      $[$docComment?:docComment]? require%$requireTk $name:depName $[@%$atTk? $ver?:verSpec]?
        $[$fromClause?:fromClause]? $[$withClause?:withClause]?) => do
    let requireTk ← fmt requireTk
    let name ← fmt name
    let atTk? ← fmt? atTk?
    let ver? ← fmt? ver?
    let fromClause? ← fmt? fromClause?
    let withClause? ← fmt? withClause?
    let dep := Layouts.infixOperator #[name, atTk?, ver?] .dense
    let decl := Layouts.blocks #[requireTk, dep, fromClause?, withClause?]
    fmtDeclWithModifiers docComment? none #[] decl
  | _ =>
    throw .partialFormatter

/--
Converts the optional simple binder of a Lake declaration signature into the binders of a
declaration signature, retaining the source information of the original syntax.
-/
def toDeclarationBinders (binder? : Option SimpleBinder) : FmtM (TSyntaxArray binderKinds) := do
  let some binder := binder?
    | return #[]
  match binder with
  | `(simpleBinder| $id:ident) =>
    return #[⟨id⟩]
  | `(simpleBinder| (%$lbTk $id:ident $[:%$typeAscriptionTk? $type?:term]? )%$rbTk) =>
    let binderType :=
      match typeAscriptionTk?, type? with
      | some typeAscriptionTk, some type =>
        mkNullNode #[typeAscriptionTk, type.raw]
      | _, _ =>
        mkNullNode
    return #[⟨mkNode ``Parser.Term.explicitBinder
      #[lbTk, mkNullNode #[id], binderType, mkNullNode, rbTk]⟩]
  | _ =>
    throw .partialFormatter

/-- Formats a Lake target or facet declaration with the keyword `kw` and the signature `sig`. -/
public def fmtWithBuildDeclSig (kw : Syntax) (sig : TSyntax ``buildDeclSig) : FmtM TaggedDoc := do
  match sig with
  | `(buildDeclSig|
      $name:identOrStr $[$binder?:simpleBinder]? :%$typeAscriptionTk $type:term :=%$colonEqTk
        $declBody:term $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) =>
    fmtAssignmentDeclaration kw none name (← toDeclarationBinders binder?) typeAscriptionTk type
      colonEqTk declBody terminationSuffix whereDecls?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.moduleFacetDecl]
public def fmtModuleFacetDecl : Fmt := fun
  | `(moduleFacetDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? module_facet%$moduleFacetTk
        $sig:buildDeclSig) => do
    let decl ← fmtWithBuildDeclSig moduleFacetTk sig
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.packageFacetDecl]
public def fmtPackageFacetDecl : Fmt := fun
  | `(packageFacetDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? package_facet%$packageFacetTk
        $sig:buildDeclSig) => do
    let decl ← fmtWithBuildDeclSig packageFacetTk sig
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.libraryFacetDecl]
public def fmtLibraryFacetDecl : Fmt := fun
  | `(libraryFacetDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? library_facet%$libraryFacetTk
        $sig:buildDeclSig) => do
    let decl ← fmtWithBuildDeclSig libraryFacetTk sig
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.targetCommand]
public def fmtTargetCommand : Fmt := fun
  | `(targetCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? target%$targetTk
        $sig:buildDeclSig) => do
    let decl ← fmtWithBuildDeclSig targetTk sig
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.externLibCommand]
public def fmtExternLibCommand : Fmt := fun
  | `(externLibCommand|
      $[$docComment?:docComment]? $[$attributes?:attributes]? extern_lib%$externLibTk
        $name:identOrStr $[$binder?:simpleBinder]? :=%$colonEqTk $declBody:term
        $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    let decl ←
      fmtAssignmentDeclaration externLibTk none name (← toDeclarationBinders binder?) none none
        colonEqTk declBody terminationSuffix whereDecls?
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.scriptDecl]
public def fmtScriptDecl : Fmt := fun
  | `(scriptDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? script%$scriptTk
        $name:identOrStr $[$binder?:simpleBinder]? :=%$colonEqTk $declBody:term
        $terminationSuffix:suffix
      $[$whereDecls?:whereDecls]?) => do
    let decl ←
      fmtAssignmentDeclaration scriptTk none name (← toDeclarationBinders binder?) none none
        colonEqTk declBody terminationSuffix whereDecls?
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | `(scriptDecl|
      $[$docComment?:docComment]? $[$attributes?:attributes]? script%$scriptTk
        $name:identOrStr $[$binder?:simpleBinder]? $declBody:do $[$whereDecls?:whereDecls]?) => do
    let decl ←
      fmtAssignmentDeclaration scriptTk none name (← toDeclarationBinders binder?) none none none
        declBody emptyTerminationSuffix whereDecls?
    fmtDeclWithModifiers docComment? attributes? #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.evalVer]
public def fmtEvalVer : Fmt := fun
  | `(evalVer| eval_ver%%$evalVerTk $ver:term) => fmtAppLike #[evalVerTk, ver]
  | _ => throw .partialFormatter

@[builtin_fmt Lake.DSL.verLit]
public def fmtVerLit : Fmt := fun
  | `(verLit| v!%$verTk$ver:interpolatedStr) => do
    let verTk ← fmt verTk
    let ver ← fmt ver
    return Layouts.strLit verTk ver
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.facetSuffix]
public def fmtFacetSuffix : Fmt := fun
  | `(facetSuffix| :%$colonTk$facet:ident) => do
    let colonTk ← fmt colonTk
    let facet ← fmt facet
    return Layouts.atomic #[colonTk, facet]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.packageTargetLit]
public def fmtPackageTargetLit : Fmt := fun
  | `(packageTargetLit| $[+%$plusTk?]?$targetId:ident) => do
    let plusTk? ← fmt? plusTk?
    let targetId ← fmt targetId
    return Layouts.atomic #[plusTk?, targetId]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.moduleTargetKeyLit]
public def fmtModuleTargetKeyLit : Fmt := fun
  | `(moduleTargetKeyLit| `+%$keyTk$mod:ident $[$facets:facetSuffix]*) => do
    let keyTk ← fmt keyTk
    let mod ← fmt mod
    let facets ← fmtArray facets
    return Layouts.atomic <| #[keyTk, mod] ++ facets
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.packageTargetKeyLit]
public def fmtPackageTargetKeyLit : Fmt := fun
  | `(packageTargetKeyLit|
      `@%$keyTk$[$pkg?:ident]?$[/%$slashTk?$targetLit?:packageTargetLit]?$[$facets:facetSuffix]*) =>
    do
      let keyTk ← fmt keyTk
      let pkg? ← fmt? pkg?
      let slashTk? ← fmt? slashTk?
      let targetLit? ← fmt? targetLit?
      let facets ← fmtArray facets
      return Layouts.atomic <| #[keyTk, pkg?, slashTk?, targetLit?] ++ facets
  | _ =>
    throw .partialFormatter

/-- The components of a `meta if` command, as deconstructed by `metaIf?`. -/
structure MetaIf where
  metaTk : Syntax
  ifTk : Syntax
  cond : TSyntax `term
  thenTk : Syntax
  thenBranch : TSyntax ``cmdDo
  elseTk? : Option Syntax
  elseBranch? : Option (TSyntax ``cmdDo)

/-- Deconstructs `stx` into the components of a `meta if` command, if it is one. -/
def deconstructMetaIf? (stx : Syntax) : Option MetaIf :=
  match stx with
  | `(metaIf|
      meta%$metaTk if%$ifTk $cond:term then%$thenTk $thenBranch:cmdDo
      $[else%$elseTk? $elseBranch?:cmdDo]?) =>
    some { metaTk, ifTk, cond, thenTk, thenBranch, elseTk?, elseBranch? }
  | _ =>
    none

/--
Formats the commands of the `then` or `else` branch introduced by `kwTk` below `head`, which is
the document of everything that precedes `kwTk`.
-/
def fmtMetaIfBranch (head : TaggedDoc) (kwTk : Syntax) (branch : TSyntax ``cmdDo)
    : FmtM TaggedDoc := do
  match branch with
  | `(cmdDo| do%$doTk $[$cmds:command]*) =>
    let doTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments doTk
    let kwTk ← fmt kwTk
    let doTk ← fmt doTk
    let cmds ← fmtArrayWithRetainedIntermediateNewlinesAndComments cmds
    -- The commands of the group must be indented so that `many1Indent` does not extend the group
    -- to the commands that follow the `meta if`.
    return nested <| Layouts.retainedWhitespace #[
      Layouts.spacedAtomic #[head, kwTk, doTk],
      doTrailingDoc,
      cmds
    ]
  | `(cmdDo| $cmd:command) =>
    let kwTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments kwTk
    let kwTk ← fmt kwTk
    let cmd ← fmt cmd
    return nested <| Layouts.retainedWhitespace #[
      Layouts.spacedAtomic #[head, kwTk],
      kwTrailingDoc,
      cmd
    ]
  | _ =>
    throw .partialFormatter

/--
Formats the branches of the `meta if` chain that starts at `c` below `head`, which is the document
of the `else` token that `c` is chained to, interleaved with the whitespace between the branches.
-/
partial def fmtMetaIfChain (head : TaggedDoc) (c : MetaIf) : FmtM (Array TaggedDoc) := do
  let metaTk ← fmt c.metaTk
  let ifTk ← fmt c.ifTk
  let cond ← fmt c.cond
  let metaIf := Layouts.spacedAtomic #[head, metaTk, ifTk]
  let condition := Layouts.pseudoApplication #[metaIf, cond]
  let «then» ← fmtMetaIfBranch condition c.thenTk c.thenBranch
  let some elseTk := c.elseTk?
    | return #[«then»]
  let some elseBranch := c.elseBranch?
    | return #[«then»]
  let thenTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments c.thenBranch
  -- A `meta if` in an `else` branch continues the chain instead of being formatted below the
  -- `else` as a `meta if` of its own.
  if let `(cmdDo| $cmd:command) := elseBranch then
    if let some c := deconstructMetaIf? cmd then
      return #[«then», thenTrailingDoc] ++ (← fmtMetaIfChain (← fmt elseTk) c)
  return #[«then», thenTrailingDoc, ← fmtMetaIfBranch empty elseTk elseBranch]

@[builtin_fmt Lake.DSL.metaIf]
public def fmtMetaIf : Fmt := fun stx => do
  let some c := deconstructMetaIf? stx
    | throw .partialFormatter
  return Layouts.retainedWhitespace <| ← fmtMetaIfChain empty c

@[builtin_fmt Lake.DSL.runIO]
public def fmtRunIO : Fmt := fun
  | `(runIO| run_io%$runIOTk $seq:doSeq) => do
    let runIOTk ← fmt runIOTk
    let seq ← fmt seq
    return Layouts.keywordPrefixedSeq runIOTk seq .nonSticky
  | _ =>
    throw .partialFormatter
