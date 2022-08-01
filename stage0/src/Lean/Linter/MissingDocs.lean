/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Elab.Tactic.Config
import Lean.Linter.Util

namespace Lean.Linter
open Elab.Command Parser.Command
open Parser.Term hiding «set_option»

register_builtin_option linter.missingDocs : Bool := {
  defValue := false
  descr := "enable the 'missing documentation' linter"
}

def getLinterMissingDocs (o : Options) : Bool := getLinterValue linter.missingDocs o

partial def missingDocs : Linter := fun stx => do
  go (getLinterMissingDocs (← getOptions)) stx
where
  lint (stx : Syntax) (msg : String) : CommandElabM Unit :=
    logWarningAt stx s!"missing doc string for {msg} [linter.missingDocs]"

  lintNamed (stx : Syntax) (msg : String) : CommandElabM Unit :=
    lint stx s!"{msg} {stx.getId}"

  lintField (parent stx : Syntax) (msg : String) : CommandElabM Unit :=
    lint stx s!"{msg} {parent.getId}.{stx.getId}"

  go (enabled : Bool) : Syntax → CommandElabM Unit
  | stx@(Syntax.node _ k args) => do
    match k with
    | ``«in» =>
      if stx[0].getKind == ``«set_option» then
        let opts ← Elab.elabSetOption stx[0][1] stx[0][2]
        withScope (fun scope => { scope with opts }) do
          go (getLinterMissingDocs opts) stx[2]
      else
        go enabled stx[2]
      return
    | ``«mutual» =>
      args[1]!.getArgs.forM (go enabled)
      return
    | _ => unless enabled do return
    match k with
    | ``declaration =>
      let #[head, rest] := args | return
      if head[2][0].getKind == ``«private» then return -- not private
      if head[0].isNone then -- no doc string
        match rest.getKind with
        | ``«abbrev» => lintNamed rest[1][0] s!"public abbrev"
        | ``«def» => lintNamed rest[1][0] "public def"
        | ``«opaque» => lintNamed rest[1][0] "public opaque"
        | ``«axiom» => lintNamed rest[1][0] "public axiom"
        | ``«inductive» => lintNamed rest[1][0] "public inductive"
        | ``classInductive => lintNamed rest[1][0] "public inductive"
        | ``«structure» => lintNamed rest[1][0] "public structure"
        | _ => pure ()
      if rest.getKind matches ``«inductive» | ``classInductive then
        for stx in rest[4].getArgs do
          let head := stx[1]
          if head[2][0].getKind != ``«private» && head[0].isNone then
            lintField rest[1][0] stx[2] "public constructor"
        unless rest[5].isNone do
          for stx in rest[5][0][1].getArgs do
            let head := stx[0]
            if head[2][0].getKind == ``«private» then return -- not private
            if head[0].isNone then -- no doc string
              lintField rest[1][0] stx[1] "computed field"
      else if rest.getKind == ``«structure» then
        unless rest[5].isNone || rest[5][2].isNone do
          for stx in rest[5][2][0].getArgs do
            let head := stx[0]
            if head[2][0].getKind != ``«private» && head[0].isNone then
              if stx.getKind == ``structSimpleBinder then
                lintField rest[1][0] stx[1] "public field"
              else
                for stx in stx[2].getArgs do
                  lintField rest[1][0] stx "public field"
    | ``«initialize» =>
      let #[head, _, rest, _] := args | return
      if rest.isNone then return
      if head[2][0].getKind != ``«private» && head[0].isNone then
        lintNamed rest[0] "initializer"
    | ``«syntax» =>
      if stx[0].isNone && stx[2][0][0].getKind != ``«local» then
        if stx[5].isNone then lint stx[3] "syntax"
        else lintNamed stx[5][0][3] "syntax"
    | ``syntaxAbbrev =>
      if stx[0].isNone then
        lintNamed stx[2] "syntax"
    | ``syntaxCat =>
      if stx[0].isNone then
        lintNamed stx[2] "syntax category"
    | ``«macro» =>
      if stx[0].isNone && stx[1][0][0].getKind != ``«local» then
        if stx[4].isNone then lint stx[2] "macro"
        else lintNamed stx[4][0][3] "macro"
    | ``«elab» =>
      if stx[0].isNone && stx[1][0][0].getKind != ``«local» then
        if stx[4].isNone then lint stx[2] "elab"
        else lintNamed stx[4][0][3] "elab"
    | ``classAbbrev =>
      let head := stx[0]
      if head[2][0].getKind != ``«private» && head[0].isNone then
        lintNamed stx[3] "class abbrev"
    | ``Parser.Tactic.declareSimpLikeTactic =>
      if stx[0].isNone then
        lintNamed stx[3] "simp-like tactic"
    | ``Option.registerBuiltinOption =>
      if stx[0].isNone then
        lintNamed stx[2] "option"
    | ``Option.registerOption =>
      if stx[0].isNone then
        lintNamed stx[2] "option"
    | ``registerSimpAttr =>
      if stx[0].isNone then
        lintNamed stx[2] "simp attr"
    | ``Elab.Tactic.configElab =>
      if stx[0].isNone then
        lintNamed stx[2] "config elab"
    | _ => return
  | _ => return

builtin_initialize addLinter missingDocs
