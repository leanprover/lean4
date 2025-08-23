/-
Copyright (c) 2023-2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude

public import Init.Data.Repr
public import Init.Data.Ord
public import Lean.DocString.Types

namespace Lean.Doc

namespace MarkdownM

public structure Context where
  inEmph : Bool := false
  inBold : Bool := false
  inLink : Bool := false
  linePrefix : String := ""

public structure State where
  priorBlocks : String := ""
  currentBlock : String := ""
  /-- Footnotes -/
  footnotes : Array (String × String) := #[]

def combineBlocks (prior current : String) :=
  if prior.isEmpty then current
  else if current.isEmpty then prior
  else if prior.endsWith "\n\n" then prior ++ current
  else if prior.endsWith "\n" then prior ++ "\n" ++ current
  else prior ++ "\n\n" ++ current

def State.endBlock (state : State) : State :=
  { state with
    priorBlocks :=
      combineBlocks state.priorBlocks state.currentBlock ++
      (if state.footnotes.isEmpty then ""
       else state.footnotes.foldl (init := "\n\n") fun s (n, txt) => s ++ s!"[^{n}]:{txt}\n\n"),
    currentBlock := "",
    footnotes := #[]
  }

def State.render (state : State) : String :=
  state.endBlock.priorBlocks

def State.push (state : State) (txt : String) : State :=
  { state with currentBlock := state.currentBlock ++ txt }

end MarkdownM

open MarkdownM in
public abbrev MarkdownM := ReaderT Context (StateM State)

public def MarkdownM.run (act : MarkdownM α) (context : Context := {}) (state : State := {}) : (α × String) :=
  let (val, state) := act context state
  (val, state.render)

public def MarkdownM.run' (act : MarkdownM Unit) (context : Context := {}) (state : State := {}) : String :=
  act.run context state |>.2

def MarkdownM.push (txt : String) : MarkdownM Unit := modify (·.push txt)

def MarkdownM.endBlock : MarkdownM Unit := modify (·.endBlock)

def MarkdownM.indent: MarkdownM α → MarkdownM α :=
  withReader fun st => { st with linePrefix := st.linePrefix ++ "  " }

public class ToMarkdown (α : Type u) where
  toMarkdown : α → MarkdownM Unit

public class MarkdownInline (i : Type u) where
  toMarkdown : (Inline i → MarkdownM Unit) → i → Array (Inline i) → MarkdownM Unit

public instance : MarkdownInline Empty where
  toMarkdown := nofun

public class MarkdownBlock (i : Type u) (b : Type v) where
  toMarkdown :
    (Inline i → MarkdownM Unit) → (Block i b → MarkdownM Unit) →
    b → Array (Block i b) → MarkdownM Unit

public instance : MarkdownBlock i Empty where
  toMarkdown := nofun


private def escape (s : String) : String := Id.run do
  let mut s' := ""
  let mut iter := s.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    if isSpecial c then
      s' := s'.push '\\'
    s' := s'.push c
  return s'
where
  isSpecial c := "*_`-+.!<>[]{}()#".any (· == c)

private def quoteCode (str : String) : String := Id.run do
  let mut longest := 0
  let mut current := 0
  let mut iter := str.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    if c == '`' then
      current := current + 1
    else
      longest := max longest current
      current := 0
  let backticks := "".pushn '`' (max longest current + 1)
  let str := if str.startsWith "`" || str.endsWith "`" then " " ++ str ++ " " else str
  backticks ++ str ++ backticks

open MarkdownM in
private partial def inlineMarkdown [MarkdownInline i] : Inline i → MarkdownM Unit
  | .text s =>
    push (escape s)
  | .linebreak s => do
    push <| s.replace "\n" ("\n" ++ (← read).linePrefix )
  | .emph xs => do
    unless (← read).inEmph do
      push "*"
    withReader (fun ρ => { ρ with inEmph := true }) do
      for i in xs do inlineMarkdown i
    unless (← read).inEmph do
      push "*"
  | .bold xs => do
    unless (← read).inEmph do
      push "**"
    withReader (fun ρ => { ρ with inEmph := true }) do
      for i in xs do inlineMarkdown i
    unless (← read).inEmph do
      push "**"
  | .concat xs =>
    for i in xs do inlineMarkdown i
  | .link content url => do
    if (← read).inLink then
      for i in content do inlineMarkdown i
    else
      push "["
      for i in content do inlineMarkdown i
      push "]("
      push url
      push ")"
  | .image alt url =>
    push s!"![{escape alt}]({url})"
  | .footnote name content => do
    push s!"[ˆ^{name}]"
    let footnoteContent := (content.forM inlineMarkdown) {} {} |>.2.render
    modify fun st => { st with footnotes := st.footnotes.push (name, footnoteContent) }
  | .code str =>
    push (quoteCode str)
  | .math .display m => push s!"$${m}$$"
  | .math .inline m => push s!"${m}$"
  | .other container content => do
    MarkdownInline.toMarkdown inlineMarkdown container content

public instance [MarkdownInline i] : ToMarkdown (Inline i) where
  toMarkdown inline := private inlineMarkdown inline

private def quoteCodeBlock (indent : Nat) (str : String) : String := Id.run do
  let mut longest := 2
  let mut current := 0
  let mut iter := str.iter
  let mut out := ""
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    if c == '`' then
      current := current + 1
    else
      longest := max longest current
      current := 0
    out := out.push c
    if c == '\n' then
      out := out.pushn ' ' indent
  let backticks := "" |>.pushn ' ' indent |>.pushn '`' (max longest current + 1)
  backticks ++ "\n" ++ out ++ "\n" ++ backticks ++ "\n"

open MarkdownM in
private partial def blockMarkdown [MarkdownInline i] [MarkdownBlock i b] : Block i b → MarkdownM Unit
  | .para xs => do
    for i in xs do
      ToMarkdown.toMarkdown i
    endBlock
  | .concat bs =>
    for b in bs do
      blockMarkdown b
  | .blockquote bs => do
    withReader (fun ρ => { ρ with linePrefix := ρ.linePrefix ++ "> " })
      for b in bs do
        blockMarkdown b
    endBlock
  | .ul items => do
    for item in items do
      push <| (← read).linePrefix ++ "* "
      withReader (fun ρ => { ρ with linePrefix := ρ.linePrefix ++ "  " }) do
        for b in item.contents do
          blockMarkdown b
    endBlock
  | .ol start items => do
    let mut n := max 1 start.toNat
    for item in items do
      push <| (← read).linePrefix ++ s!"{n}. "
      withReader (fun ρ => { ρ with linePrefix := ρ.linePrefix ++ "  " }) do
        for b in item.contents do
          blockMarkdown b
      n := n + 1
    endBlock
  | .dl items => do
    for item in items do
      push <| (← read).linePrefix ++ "* "
      withReader (fun ρ => { ρ with linePrefix := ρ.linePrefix ++ "  " }) do
        inlineMarkdown (.bold item.term)
        inlineMarkdown (.text ": " : Inline i)
        push "\n"
        push (← read).linePrefix
        blockMarkdown (.concat item.desc)
    endBlock
  | .code str => do
    unless (← get).currentBlock.isEmpty || (← get).currentBlock.endsWith "\n" do
      push "\n"
    push <| quoteCodeBlock (← read).linePrefix.length str
    endBlock
  | .other container content =>
    MarkdownBlock.toMarkdown (i := i) (b := b) inlineMarkdown blockMarkdown container content


public instance [MarkdownInline i] [MarkdownBlock i b] : ToMarkdown (Block i b) where
  toMarkdown block := private blockMarkdown block

open MarkdownM in
open ToMarkdown in
private partial def partMarkdown [MarkdownInline i] [MarkdownBlock i b] (level : Nat) (part : Part i b p) : MarkdownM Unit := do
  push ("".pushn '#' (level + 1))
  push " "
  for i in part.title do
    toMarkdown i
  endBlock
  for b in part.content do
    toMarkdown b
  endBlock
  for p in part.subParts do
    partMarkdown (level + 1) p

public instance [MarkdownInline i] [MarkdownBlock i b] : ToMarkdown (Part i b p) where
  toMarkdown part := private partMarkdown 0 part
