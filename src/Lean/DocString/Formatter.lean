/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module
prelude
public import Lean.PrettyPrinter.Formatter
import Lean.DocString.Parser


namespace Lean.Doc.Parser

open Lean.PrettyPrinter Formatter
open Lean.Syntax.MonadTraverser

open Lean.Doc.Syntax

def atomString : Syntax → String
  | .node _ _ #[x] => atomString x
  | .atom _ x => x
  | stx => s!"NON-ATOM {stx}"

def pushAtomString : Formatter := do
  push <| atomString (← getCur)
  goLeft

def pushAtomStrLit : Formatter := do
  push <| (Syntax.decodeStrLit (atomString (← getCur))).getD ""
  goLeft


def identString : Syntax → String
  | .node _ _ #[x] => identString x
  | .ident _ _ x _ => toString x
  | stx => s!"NON-IDENT {stx}"

def pushIdent : Formatter := do
  push <| identString (← getCur)
  goLeft

def rep (f : Formatter) : Formatter := concat do
  let count := (← getCur).getArgs.size
  visitArgs do count.forM fun _ _ => do f

partial def versoSyntaxToString' (stx : Syntax) : ReaderT Nat (StateM String) Unit := do
  if stx.getKind == nullKind then
    stx.getArgs.forM versoSyntaxToString'
  else
    match stx with
    | `(arg_val|$s:str) => out <| atomString s
    | `(arg_val|$n:num) => out <| atomString n
    | `(arg_val|$x:ident) => out <| identString x
    | `(doc_arg|($x := $v)) | `(doc_arg|$x:ident := $v) =>
      out "("
      out <| identString x
      out " := "
      versoSyntaxToString' v
      out ")"
    | `(doc_arg|+%$tk$x:ident) | `(doc_arg|-%$tk$x:ident) =>
      out <| atomString tk
      out <| identString x
    | `(doc_arg|$x:arg_val) => versoSyntaxToString' x
    | `(inline|$s:str) => out s.getString
    | `(inline|_[%$tk1 $inl* ]%$tk2) | `(inline|*[%$tk1 $inl* ]%$tk2) =>
      out <| atomString tk1
      inl.forM versoSyntaxToString'
      out <| atomString tk2
    | `(inline|link[%$tk1 $inl* ]%$tk2 $tgt) =>
      out <| atomString tk1
      inl.forM versoSyntaxToString'
      out <| atomString tk2
      versoSyntaxToString' tgt
    | `(inline|image(%$tk1 $alt )%$tk2 $tgt) =>
      out <| atomString tk1
      out <| (Syntax.decodeStrLit (atomString alt)).getD ""
      out <| atomString tk2
      versoSyntaxToString' tgt
    | `(inline|role{$name $args*}[$inls*]) =>
      out "{"
      out <| identString name
      for arg in args do
        out " "
        versoSyntaxToString' arg
      out "}["
      inls.forM versoSyntaxToString'
      out "]"
    | `(inline|code(%$tk1$s)%$tk2) =>
      out <| atomString tk1
      out <| (Syntax.decodeStrLit (atomString s)).getD ""
      out <| atomString tk2
    | `(inline|footnote(%$tk1 $ref )%$tk2) =>
      out <| atomString tk1
      out <| (Syntax.decodeStrLit (atomString ref)).getD ""
      out <| atomString tk2
    | `(inline|line! $s) =>
      out <| (Syntax.decodeStrLit (atomString s)).getD ""
    | `(inline|\math%$tk1 code(%$tk2 $s )%$tk3)
    | `(inline|\displaymath%$tk1 code(%$tk2 $s )%$tk3) =>
      out <| atomString tk1
      out <| atomString tk2
      out <| (Syntax.decodeStrLit (atomString s)).getD ""
      out <| atomString tk3
    | `(link_target|[%$tk1 $ref ]%$tk2) =>
      out <| atomString tk1
      out <| (Syntax.decodeStrLit (atomString ref)).getD ""
      out <| atomString tk2
    | `(link_target|(%$tk1 $url )%$tk2) =>
      out <| atomString tk1
      out <| (Syntax.decodeStrLit (atomString url)).getD ""
      out <| atomString tk2
    | `(block|header($n){$inl*}) =>
      out <| "#".pushn '#' n.getNat ++ " "
      inl.forM versoSyntaxToString'
      endBlock
    | `(block|para[$inl*]) =>
      startBlock
      inl.forM versoSyntaxToString'
      endBlock
    | `(block|ul{$items*}) =>
      startBlock
      items.forM fun
        | `(list_item|* $blks*) => do
          out "* "
          withReader (· + 2) (blks.forM versoSyntaxToString')
          endBlock
        | _ => pure ()
      endBlock
    | `(block|ol($n){$items*}) =>
      startBlock
      let mut n := n.getNat
      for item in items do
        match item with
        | `(list_item|* $blks*) => do
          out s!"{n}. "
          withReader (· + 2) (blks.forM versoSyntaxToString')
          endBlock
          n := n + 1
        | _ => pure ()
      endBlock
    | `(block| > $blks*) =>
      startBlock
      out "> "
      withReader (· + 2) (blks.forM versoSyntaxToString')
      endBlock
    | `(block| ```%$tk1 $name $args* | $s ```%$tk2) =>
      startBlock
      out <| atomString tk1
      out <| identString name
      for arg in args do
        out " "
        versoSyntaxToString' arg
      out "\n"
      let i ← read
      let s := Syntax.decodeStrLit (atomString s) |>.getD ""
        |>.split '\n'
        |>.map (fun (s : String.Slice) => "".pushn ' ' i ++ s)
        |>.toList
        |> "\n".intercalate
      out s
      out <| "".pushn ' ' i
      out <| atomString tk2
      endBlock
    | `(block| :::%$tk1 $name $args* {$blks*}%$tk2) =>
      startBlock
      out <| atomString tk1
      out " "
      out <| identString name
      for arg in args do
        out " "
        versoSyntaxToString' arg
      out "\n"
      blks.forM versoSyntaxToString'
      let i ← read
      out <| "".pushn ' ' i
      out <| atomString tk2
      endBlock
    | `(block|command{ $name $args* }) =>
      startBlock
      out <| "{"
      out <| identString name
      for arg in args do
        out " "
        versoSyntaxToString' arg
      out "}"
      endBlock

    | other => out (toString other)
where
  out (s : String) : ReaderT Nat (StateM String) Unit := modify (· ++ s)
  nl : ReaderT Nat (StateM String) Unit := read >>= fun n => modify (· ++ "\n".pushn ' ' n)
  startBlock : ReaderT Nat (StateM String) Unit := do
    let s ← get
    if s.endsWith "\n" then
      let i ← read
      out ("".pushn ' ' i)
  endBlock : ReaderT Nat (StateM String) Unit := do
    let s ← get
    if s.endsWith "\n\n" then return
    else if s.endsWith "\n" then out "\n"
    else out "\n\n"

def formatMetadata : Formatter := do
  visitArgs do
    pushLine
    visitAtom .anonymous
    pushLine
    Parser.metadataContents.formatter
    pushLine
    visitAtom .anonymous

def versoSyntaxToString (stx : Syntax) : String :=
  versoSyntaxToString' stx |>.run 0 |>.run "" |>.2

public def document.formatter : Formatter := concat do
  let stx ← getCur
  let i := stx.getArgs.size
  visitArgs do
    for _ in [0:i] do
      let blk ← getCur
      if blk.getKind == ``Doc.Syntax.metadata_block then
        formatMetadata
      else
        push (versoSyntaxToString blk)
        goLeft
