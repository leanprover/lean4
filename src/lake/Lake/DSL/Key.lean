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

syntax facetSuffix := ":" noWs ident

syntax:max "`+" noWs ident facetSuffix* : term
syntax:max "`@" noWs (ident)? (noWs "/" noWs ident)? facetSuffix* : term
syntax:max "`/" noWs ident facetSuffix* : term
syntax:max "`:" noWs ident facetSuffix* : term

private def addFacets (tgt : Term) (facets : Array Ident) : MacroM Term := do
  let facetLits := facets.map fun facet => Name.quoteFrom facet facet.getId
  facetLits.foldlM (init := tgt) fun tgt lit => `(BuildKey.facet $tgt $lit)

macro_rules
| `(`+%$tk$mod$[:$facets]*) => withRef tk do
  let modLit := Name.quoteFrom mod mod.getId
  let tgt ← `(BuildKey.module $modLit)
  addFacets tgt facets
| `(`@%$tk$(pkg?)?$[/$tgt?]?$[:$facets]*) => withRef tk do
  let pkgLit :=
    if let some pkg := pkg? then
      Name.quoteFrom pkg pkg.getId
    else
      Name.quoteFrom tk Name.anonymous
  let tgt ←
    if let some tgt := tgt? then
      let tgtLit := Name.quoteFrom tgt tgt.getId
      `(BuildKey.packageTarget $pkgLit $tgtLit)
    else
      `(BuildKey.package $pkgLit)
  addFacets tgt facets
| `(`/%$tk$tgt$[:$facets]*) => withRef tk do
  let pkgLit := Name.quoteFrom tk Name.anonymous
  let tgtLit := Name.quoteFrom tgt tgt.getId
  let tgt ← `(BuildKey.packageTarget $pkgLit $tgtLit)
  addFacets tgt facets
| `(`:%$tk$facet$[:$facets]*) => withRef tk do
  let pkgLit := Name.quoteFrom tk Name.anonymous
  let tgt ← `(BuildKey.package $pkgLit)
  addFacets tgt (#[facet] ++ facets)
