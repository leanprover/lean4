/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Key

/-! # DSL for Build Key
Notation for specifying build keys in a package.
-/

open Lean

namespace Lake.DSL

syntax facetSuffix := atomic(":" noWs) ident
syntax packageTargetLit := atomic("+" noWs)? ident

/-- A module target key literal (with optional facet). -/
scoped syntax:max "`+" noWs ident facetSuffix* : term

/-- A package target key literal (with optional facet). -/
scoped syntax:max "`@" (noWs ident)?
  (atomic(noWs "/" noWs) packageTargetLit)? (noWs facetSuffix)* : term

private def expandFacets (tgt : Term) (facets : Array Ident) : MacroM Term := do
  let facetLits := facets.map fun facet => Name.quoteFrom facet facet.getId
  facetLits.foldlM (init := tgt) fun tgt lit => `(BuildKey.facet $tgt $lit)

private def expandPackageTargetLit
  (pkg : Term) (stx : TSyntax ``packageTargetLit)
: MacroM Term := withRef stx do
  let `(packageTargetLit|$[+%$mod?]?$tgt) := stx
    | Macro.throwError "ill-formed package target literal"
  let tgtName :=
    if mod?.isSome then
      tgt.getId ++ PartialBuildKey.moduleTargetIndicator
    else
      tgt.getId
  let tgtLit := Name.quoteFrom tgt tgtName
  `(BuildKey.packageTarget $pkg $tgtLit)

macro_rules
| `(`+%$tk$mod$[:$facets]*) => withRef tk do
  let modLit := Name.quoteFrom mod mod.getId
  let tgt ← `(BuildKey.module $modLit)
  let key ← expandFacets tgt facets
  `(PartialBuildKey.mk $key)
| `(`@%$tk$(pkg?)?$[/$tgt?]?$[:$facets]*) => withRef tk do
  let pkgLit :=
    if let some pkg := pkg? then
      Name.quoteFrom pkg pkg.getId
    else
      Name.quoteFrom tk Name.anonymous
  let tgt ←
    if let some tgt := tgt? then
      expandPackageTargetLit pkgLit tgt
    else
      `(BuildKey.package $pkgLit)
  let key ← expandFacets tgt facets
  `(PartialBuildKey.mk $key)
