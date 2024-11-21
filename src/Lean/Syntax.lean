/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Data.Range
import Init.Data.Hashable
import Lean.Data.Name
import Lean.Data.Format

/--
A position range inside a string. This type is mostly in combination with syntax trees,
as there might not be a single underlying string in this case that could be used for a `Substring`.
-/
protected structure String.Range where
  start : String.Pos
  stop  : String.Pos
  deriving Inhabited, Repr, BEq, Hashable

def String.Range.contains (r : String.Range) (pos : String.Pos) (includeStop := false) : Bool :=
  r.start <= pos && (if includeStop then pos <= r.stop else pos < r.stop)

def String.Range.includes (super sub : String.Range) : Bool :=
  super.start <= sub.start && super.stop >= sub.stop

namespace Lean

def SourceInfo.updateTrailing (trailing : Substring) : SourceInfo → SourceInfo
  | SourceInfo.original leading pos _ endPos => SourceInfo.original leading pos trailing endPos
  | info                                     => info

def SourceInfo.getRange? (canonicalOnly := false) (info : SourceInfo) : Option String.Range :=
  return ⟨(← info.getPos? canonicalOnly), (← info.getTailPos? canonicalOnly)⟩

deriving instance BEq for SourceInfo

/-! # Syntax AST -/

inductive IsNode : Syntax → Prop where
  | mk (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : IsNode (Syntax.node info kind args)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def unreachIsNodeMissing {β} : IsNode Syntax.missing → β := nofun
def unreachIsNodeAtom {β} {info val} : IsNode (Syntax.atom info val) → β := nofun
def unreachIsNodeIdent {β info rawVal val preresolved} : IsNode (Syntax.ident info rawVal val preresolved) → β := nofun

def isLitKind (k : SyntaxNodeKind) : Bool :=
  k == strLitKind || k == numLitKind || k == charLitKind || k == nameLitKind || k == scientificLitKind

namespace SyntaxNode

@[inline] def getKind (n : SyntaxNode) : SyntaxNodeKind :=
  match n with
  | ⟨Syntax.node _ k _, _⟩  => k
  | ⟨Syntax.missing, h⟩     => unreachIsNodeMissing h
  | ⟨Syntax.atom .., h⟩     => unreachIsNodeAtom h
  | ⟨Syntax.ident .., h⟩    => unreachIsNodeIdent h

@[inline] def withArgs {β} (n : SyntaxNode) (fn : Array Syntax → β) : β :=
  match n with
  | ⟨Syntax.node _ _ args, _⟩   => fn args
  | ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
  | ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
  | ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h

@[inline] def getNumArgs (n : SyntaxNode) : Nat :=
  withArgs n fun args => args.size

@[inline] def getArg (n : SyntaxNode) (i : Nat) : Syntax :=
  withArgs n fun args => args.get! i

@[inline] def getArgs (n : SyntaxNode) : Array Syntax :=
  withArgs n fun args => args

@[inline] def modifyArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
  match n with
  | ⟨Syntax.node i k args, _⟩  => Syntax.node i k (fn args)
  | ⟨Syntax.missing, h⟩        => unreachIsNodeMissing h
  | ⟨Syntax.atom _ _, h⟩       => unreachIsNodeAtom h
  | ⟨Syntax.ident _ _ _ _,  h⟩ => unreachIsNodeIdent h

end SyntaxNode

namespace Syntax

/--
Compares syntax structures and position ranges, but not whitespace. We generally assume that if
syntax trees equal in this way generate the same elaboration output, including positions contained
in e.g. diagnostics and the info tree. However, as we have a few request handlers such as `goalsAt?`
that are sensitive to whitespace information in the info tree, we currently use `eqWithInfo` instead
for reuse checks.
-/
partial def structRangeEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node info k args, .node info' k' args' =>
    info.getRange? == info'.getRange? && k == k' && args.isEqv args' structRangeEq
  | .atom info val, .atom info' val' => info.getRange? == info'.getRange? && val == val'
  | .ident info rawVal val preresolved, .ident info' rawVal' val' preresolved' =>
    info.getRange? == info'.getRange? && rawVal == rawVal' && val == val' &&
    preresolved == preresolved'
  | _, _ => false

/-- Like `structRangeEq` but prints trace on failure if `trace.Elab.reuse` is activated. -/
def structRangeEqWithTraceReuse (opts : Options) (stx1 stx2 : Syntax) : Bool :=
  if stx1.structRangeEq stx2 then
    true
  else
    if opts.getBool `trace.Elab.reuse then
      dbg_trace "reuse stopped:
{stx1.formatStx (showInfo := true)} !=
{stx2.formatStx (showInfo := true)}"
      false
    else
      false


/-- Full comparison of syntax structures and source infos.  -/
partial def eqWithInfo : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node info k args, .node info' k' args' =>
    info == info' && k == k' && args.isEqv args' eqWithInfo
  | .atom info val, .atom info' val' => info == info' && val == val'
  | .ident info rawVal val preresolved, .ident info' rawVal' val' preresolved' =>
    info == info' && rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false

/-- Like `eqWithInfo` but prints trace on failure if `trace.Elab.reuse` is activated. -/
def eqWithInfoAndTraceReuse (opts : Options) (stx1 stx2 : Syntax) : Bool :=
  if stx1.eqWithInfo stx2 then
    true
  else
    if opts.getBool `trace.Elab.reuse then
      dbg_trace "reuse stopped:
{stx1.formatStx (showInfo := true)} !=
{stx2.formatStx (showInfo := true)}"
      false
    else
      false

def getAtomVal : Syntax → String
  | atom _ val => val
  | _          => ""

def setAtomVal : Syntax → String → Syntax
  | atom info _, v => (atom info v)
  | stx,         _ => stx

@[inline] def ifNode {β} (stx : Syntax) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
  match stx with
  | Syntax.node i k args => hyes ⟨Syntax.node i k args, IsNode.mk i k args⟩
  | _                    => hno ()

@[inline] def ifNodeKind {β} (stx : Syntax) (kind : SyntaxNodeKind) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
  match stx with
  | Syntax.node i k args => if k == kind then hyes ⟨Syntax.node i k args, IsNode.mk i k args⟩ else hno ()
  | _                    => hno ()

def asNode : Syntax → SyntaxNode
  | Syntax.node info kind args => ⟨Syntax.node info kind args, IsNode.mk info kind args⟩
  | _                          => ⟨mkNullNode, IsNode.mk _ _ _⟩

def getIdAt (stx : Syntax) (i : Nat) : Name :=
  (stx.getArg i).getId

/--
Check for a `Syntax.ident` of the given name anywhere in the tree.
This is usually a bad idea since it does not check for shadowing bindings,
but in the delaborator we assume that bindings are never shadowed.
-/
partial def hasIdent (id : Name) : Syntax → Bool
  | ident _ _ id' _ => id == id'
  | node _ _ args   => args.any (hasIdent id)
  | _               => false

@[inline] def modifyArgs (stx : Syntax) (fn : Array Syntax → Array Syntax) : Syntax :=
  match stx with
  | node i k args => node i k (fn args)
  | stx           => stx

@[inline] def modifyArg (stx : Syntax) (i : Nat) (fn : Syntax → Syntax) : Syntax :=
  match stx with
  | node info k args => node info k (args.modify i fn)
  | stx              => stx

@[specialize] partial def replaceM {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) : Syntax → m (Syntax)
  | stx@(node info kind args) => do
    match (← fn stx) with
    | some stx => return stx
    | none     => return node info kind (← args.mapM (replaceM fn))
  | stx => do
    let o ← fn stx
    return o.getD stx

@[specialize] partial def rewriteBottomUpM {m : Type → Type} [Monad m] (fn : Syntax → m (Syntax)) : Syntax → m (Syntax)
  | node info kind args   => do
    let args ← args.mapM (rewriteBottomUpM fn)
    fn (node info kind args)
  | stx => fn stx

@[inline] def rewriteBottomUp (fn : Syntax → Syntax) (stx : Syntax) : Syntax :=
  Id.run <| stx.rewriteBottomUpM fn

private def updateInfo : SourceInfo → String.Pos → String.Pos → SourceInfo
  | SourceInfo.original lead pos trail endPos, leadStart, trailStop =>
    SourceInfo.original { lead with startPos := leadStart } pos { trail with stopPos := trailStop } endPos
  | info, _, _ => info

private def chooseNiceTrailStop (trail : Substring) : String.Pos :=
trail.startPos + trail.posOf '\n'

/-- Remark: the State `String.Pos` is the `SourceInfo.trailing.stopPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux : Syntax → StateM String.Pos (Option Syntax)
  | atom info@(SourceInfo.original _ _ trail _) val => do
    let trailStop := chooseNiceTrailStop trail
    let newInfo := updateInfo info (← get) trailStop
    set trailStop
    return some (atom newInfo val)
  | ident info@(SourceInfo.original _ _ trail _) rawVal val pre => do
    let trailStop := chooseNiceTrailStop trail
    let newInfo := updateInfo info (← get) trailStop
    set trailStop
    return some (ident newInfo rawVal val pre)
  | _ => pure none

/-- Set `SourceInfo.leading` according to the trailing stop of the preceding token.
    The result is a round-tripping syntax tree IF, in the input syntax tree,
    * all leading stops, atom contents, and trailing starts are correct
    * trailing stops are between the trailing start and the next leading stop.

    Remark: after parsing, all `SourceInfo.leading` fields are empty.
    The `Syntax` argument is the output produced by the parser for `source`.
    This function "fixes" the `source.leading` field.

    Additionally, we try to choose "nicer" splits between leading and trailing stops
    according to some heuristics so that e.g. comments are associated to the (intuitively)
    correct token.

    Note that the `SourceInfo.trailing` fields must be correct.
    The implementation of this Function relies on this property. -/
def updateLeading : Syntax → Syntax :=
  fun stx => (replaceM updateLeadingAux stx).run' 0

partial def updateTrailing (trailing : Substring) : Syntax → Syntax
  | Syntax.atom info val               => Syntax.atom (info.updateTrailing trailing) val
  | Syntax.ident info rawVal val pre   => Syntax.ident (info.updateTrailing trailing) rawVal val pre
  | n@(Syntax.node info k args)        =>
    if h : args.size = 0 then n
    else
     let i    := args.size - 1
     let last := updateTrailing trailing args[i]
     let args := args.set i last;
     Syntax.node info k args
  | s => s

open SourceInfo in
/-- Split an `ident` into its dot-separated components while preserving source info.
Macro scopes are first erased.  For example, `` `foo.bla.boo._@._hyg.4 `` ↦ `` [`foo, `bla, `boo] ``.
If `nFields` is set, we take that many fields from the end and keep the remaining components
as one name. For example, `` `foo.bla.boo `` with `(nFields := 1)` ↦ `` [`foo.bla, `boo] ``. -/
def identComponents (stx : Syntax) (nFields? : Option Nat := none) : List Syntax :=
  match stx with
  | ident si@(SourceInfo.original lead pos trail _) rawStr val _ => Id.run do
    let val := val.eraseMacroScopes
    -- With original info, we assume that `rawStr` represents `val`.
    let nameComps := nameComps val nFields?
    let rawComps := splitNameLit rawStr
    if !rawComps.isEmpty then
      let rawComps :=
        if let some nFields := nFields? then
          let nPrefix := rawComps.length - nFields
          let prefixSz := rawComps.take nPrefix |>.foldl (init := 0) fun acc (ss : Substring) => acc + ss.bsize + 1
          let prefixSz := prefixSz - 1 -- The last component has no dot
          rawStr.extract 0 ⟨prefixSz⟩ :: rawComps.drop nPrefix
        else
          rawComps
      if nameComps.length == rawComps.length then
        return nameComps.zip rawComps |>.map fun (id, ss) =>
          let off := ss.startPos - rawStr.startPos
          let lead := if off == 0 then lead else "".toSubstring
          let trail := if ss.stopPos == rawStr.stopPos then trail else "".toSubstring
          let info := original lead (pos + off) trail (pos + off + ⟨ss.bsize⟩)
          ident info ss id []
    -- if re-parsing failed, just give them all the same span
    nameComps.map fun n => ident si n.toString.toSubstring n []
  | ident si _ val _ =>
    let val := val.eraseMacroScopes
    /- With non-original info:
     - `rawStr` can take all kinds of forms so we only use `val`.
     - there is no source extent to offset, so we pass it as-is. -/
    nameComps val nFields? |>.map fun n => ident si n.toString.toSubstring n []
  | _ => unreachable!
  where
    nameComps (n : Name) (nFields? : Option Nat) : List Name :=
      if let some nFields := nFields? then
        let nameComps := n.components
        let nPrefix := nameComps.length - nFields
        let namePrefix := nameComps.take nPrefix |>.foldl (init := Name.anonymous) fun acc n => acc ++ n
        namePrefix :: nameComps.drop nPrefix
      else
        n.components

structure TopDown where
  firstChoiceOnly : Bool
  stx : Syntax

/--
`for _ in stx.topDown` iterates through each node and leaf in `stx` top-down, left-to-right.
If `firstChoiceOnly` is `true`, only visit the first argument of each choice node.
-/
def topDown (stx : Syntax) (firstChoiceOnly := false) : TopDown := ⟨firstChoiceOnly, stx⟩

partial instance : ForIn m TopDown Syntax where
  forIn := fun ⟨firstChoiceOnly, stx⟩ init f => do
    let rec @[specialize] loop stx b [Inhabited (type_of% b)] := do
      match (← f stx b) with
      | ForInStep.yield b' =>
        let mut b := b'
        if let Syntax.node _ k args := stx then
          if firstChoiceOnly && k == choiceKind then
            return ← loop args[0]! b
          else
            for arg in args do
              match (← loop arg b) with
              | ForInStep.yield b' => b := b'
              | ForInStep.done b'  => return ForInStep.done b'
        return ForInStep.yield b
      | ForInStep.done b => return ForInStep.done b
    match (← @loop stx init ⟨init⟩) with
    | ForInStep.yield b => return b
    | ForInStep.done b  => return b

partial def reprint (stx : Syntax) : Option String := do
  let mut s := ""
  for stx in stx.topDown (firstChoiceOnly := true) do
    match stx with
    | atom info val           => s := s ++ reprintLeaf info val
    | ident info rawVal _ _   => s := s ++ reprintLeaf info rawVal.toString
    | node _    kind args     =>
      if kind == choiceKind then
        -- this visit the first arg twice, but that should hardly be a problem
        -- given that choice nodes are quite rare and small
        let s0 ← reprint args[0]!
        for arg in args[1:] do
          let s' ← reprint arg
          guard (s0 == s')
    | _ => pure ()
  return s
where
  reprintLeaf (info : SourceInfo) (val : String) : String :=
    match info with
    | SourceInfo.original lead _ trail _ => s!"{lead}{val}{trail}"
    -- no source info => add gracious amounts of whitespace to definitely separate tokens
    -- Note that the proper pretty printer does not use this function.
    -- The parser as well always produces source info, so round-tripping is still
    -- guaranteed.
    | _                                => s!" {val} "

def hasMissing (stx : Syntax) : Bool := Id.run do
  for stx in stx.topDown do
    if stx.isMissing then
      return true
  return false

def getRange? (stx : Syntax) (canonicalOnly := false) : Option String.Range :=
  match stx.getPos? canonicalOnly, stx.getTailPos? canonicalOnly with
  | some start, some stop => some { start, stop }
  | _,          _         => none

/-- Returns a synthetic Syntax which has the specified `String.Range`. -/
def ofRange (range : String.Range) (canonical := true) : Lean.Syntax :=
  .atom (.synthetic range.start range.stop canonical) ""

/--
Represents a cursor into a syntax tree that can be read, written, and advanced down/up/left/right.
Indices are allowed to be out-of-bound, in which case `cur` is `Syntax.missing`.
If the `Traverser` is used linearly, updates are linear in the `Syntax` object as well.
-/
structure Traverser where
  cur     : Syntax
  parents : Array Syntax
  idxs    : Array Nat

namespace Traverser

def fromSyntax (stx : Syntax) : Traverser :=
  ⟨stx, #[], #[]⟩

def setCur (t : Traverser) (stx : Syntax) : Traverser :=
  { t with cur := stx }

/-- Advance to the `idx`-th child of the current node. -/
def down (t : Traverser) (idx : Nat) : Traverser :=
  if idx < t.cur.getNumArgs then
    { cur := t.cur.getArg idx, parents := t.parents.push <| t.cur.setArg idx default, idxs := t.idxs.push idx }
  else
    { cur := Syntax.missing, parents := t.parents.push t.cur, idxs := t.idxs.push idx }

/-- Advance to the parent of the current node, if any. -/
def up (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    let cur := if t.idxs.back! < t.parents.back!.getNumArgs then t.parents.back!.setArg t.idxs.back! t.cur else t.parents.back!
    { cur := cur, parents := t.parents.pop, idxs := t.idxs.pop }
  else
    t

/-- Advance to the left sibling of the current node, if any. -/
def left (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    t.up.down (t.idxs.back! - 1)
  else
    t

/-- Advance to the right sibling of the current node, if any. -/
def right (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    t.up.down (t.idxs.back! + 1)
  else
    t

end Traverser

/-- Monad class that gives read/write access to a `Traverser`. -/
class MonadTraverser (m : Type → Type) where
  st : MonadState Traverser m

namespace MonadTraverser

variable {m : Type → Type} [Monad m] [t : MonadTraverser m]

def getCur : m Syntax := Traverser.cur <$> t.st.get
def setCur (stx : Syntax) : m Unit := @modify _ _ t.st (fun t => t.setCur stx)
def goDown (idx : Nat)    : m Unit := @modify _ _ t.st (fun t => t.down idx)
def goUp                  : m Unit := @modify _ _ t.st (fun t => t.up)
def goLeft                : m Unit := @modify _ _ t.st (fun t => t.left)
def goRight               : m Unit := @modify _ _ t.st (fun t => t.right)

def getIdx : m Nat := do
  let st ← t.st.get
  return st.idxs.back?.getD 0

end MonadTraverser
end Syntax

namespace SyntaxNode

@[inline] def getIdAt (n : SyntaxNode) (i : Nat) : Name :=
  (n.getArg i).getId

end SyntaxNode

def mkListNode (args : Array Syntax) : Syntax :=
  mkNullNode args

namespace Syntax

-- quotation node kinds are formed from a unique quotation name plus "quot"
def isQuot : Syntax → Bool
  | Syntax.node _ (Name.str _ "quot")           _ => true
  | Syntax.node _ `Lean.Parser.Term.dynamicQuot _ => true
  | _                                             => false

def getQuotContent (stx : Syntax) : Syntax :=
  let stx := if stx.getNumArgs == 1 then stx[0] else stx
  if stx.isOfKind `Lean.Parser.Term.dynamicQuot then
    stx[3]
  else
    stx[1]

-- antiquotation node kinds are formed from the original node kind (if any) plus "antiquot"
def isAntiquot : Syntax → Bool
  | .node _ (.str _ "antiquot") _ => true
  | _                             => false

def isAntiquots (stx : Syntax) : Bool :=
  stx.isAntiquot || (stx.isOfKind choiceKind && stx.getNumArgs > 0 && stx.getArgs.all isAntiquot)

def getCanonicalAntiquot (stx : Syntax) : Syntax :=
  if stx.isOfKind choiceKind then
    stx[0]
  else
    stx

def mkAntiquotNode (kind : Name) (term : Syntax) (nesting := 0) (name : Option String := none) (isPseudoKind := false) : Syntax :=
  let nesting := mkNullNode (mkArray nesting (mkAtom "$"))
  let term :=
    if term.isIdent then term
    else if term.isOfKind `Lean.Parser.Term.hole then term[0]
    else mkNode `antiquotNestedExpr #[mkAtom "(", term, mkAtom ")"]
  let name := match name with
    | some name => mkNode `antiquotName #[mkAtom ":", mkAtom name]
    | none      => mkNullNode
  mkNode (kind ++ (if isPseudoKind then `pseudo else Name.anonymous) ++ `antiquot) #[mkAtom "$", nesting, term, name]

-- Antiquotations can be escaped as in `$$x`, which is useful for nesting macros. Also works for antiquotation splices.
def isEscapedAntiquot (stx : Syntax) : Bool :=
  !stx[1].getArgs.isEmpty

-- Also works for antiquotation splices.
def unescapeAntiquot (stx : Syntax) : Syntax :=
  if isAntiquot stx then
    stx.setArg 1 <| mkNullNode stx[1].getArgs.pop
  else
    stx

-- Also works for token antiquotations.
def getAntiquotTerm (stx : Syntax) : Syntax :=
  let e := if stx.isAntiquot then stx[2] else stx[3]
  if e.isIdent then e
  else if e.isAtom then mkNode `Lean.Parser.Term.hole #[e]
  else
    -- `e` is from `"(" >> termParser >> ")"`
    e[1]

/-- Return kind of parser expected at this antiquotation, and whether it is a "pseudo" kind (see `mkAntiquot`). -/
def antiquotKind? : Syntax → Option (SyntaxNodeKind × Bool)
  | .node _ (.str (.str k "pseudo") "antiquot") _ => (k, true)
  | .node _ (.str k                 "antiquot") _ => (k, false)
  | _                                             => none

def antiquotKinds (stx : Syntax) : List (SyntaxNodeKind × Bool) :=
  if stx.isOfKind choiceKind then
    stx.getArgs.filterMap antiquotKind? |>.toList
  else
    match antiquotKind? stx with
    | some stx => [stx]
    | none     => []

-- An "antiquotation splice" is something like `$[...]?` or `$[...]*`.
def antiquotSpliceKind? : Syntax → Option SyntaxNodeKind
  | .node _ (.str k "antiquot_scope") _ => some k
  | _ => none

def isAntiquotSplice (stx : Syntax) : Bool :=
  antiquotSpliceKind? stx |>.isSome

def getAntiquotSpliceContents (stx : Syntax) : Array Syntax :=
  stx[3].getArgs

-- `$[..],*` or `$x,*` ~> `,*`
def getAntiquotSpliceSuffix (stx : Syntax) : Syntax :=
  if stx.isAntiquotSplice then
    stx[5]
  else
    stx[1]

def mkAntiquotSpliceNode (kind : SyntaxNodeKind) (contents : Array Syntax) (suffix : String) (nesting := 0) : Syntax :=
  let nesting := mkNullNode (mkArray nesting (mkAtom "$"))
  mkNode (kind ++ `antiquot_splice) #[mkAtom "$", nesting, mkAtom "[", mkNullNode contents, mkAtom "]", mkAtom suffix]

-- `$x,*` etc.
def antiquotSuffixSplice? : Syntax → Option SyntaxNodeKind
  | .node _ (.str k "antiquot_suffix_splice") _ => some k
  | _ => none

def isAntiquotSuffixSplice (stx : Syntax) : Bool :=
  antiquotSuffixSplice? stx |>.isSome

-- `$x` in the example above
def getAntiquotSuffixSpliceInner (stx : Syntax) : Syntax :=
  stx[0]

def mkAntiquotSuffixSpliceNode (kind : SyntaxNodeKind) (inner : Syntax) (suffix : String) : Syntax :=
  mkNode (kind ++ `antiquot_suffix_splice) #[inner, mkAtom suffix]

def isTokenAntiquot (stx : Syntax) : Bool :=
  stx.isOfKind `token_antiquot

def isAnyAntiquot (stx : Syntax) : Bool :=
  stx.isAntiquot || stx.isAntiquotSplice || stx.isAntiquotSuffixSplice || stx.isTokenAntiquot

/-- List of `Syntax` nodes in which each succeeding element is the parent of
the current. The associated index is the index of the preceding element in the
list of children of the current element. -/
protected abbrev Stack := List (Syntax × Nat)

/-- Return stack of syntax nodes satisfying `visit`, starting with such a node that also fulfills `accept` (default "is leaf"), and ending with the root. -/
partial def findStack? (root : Syntax) (visit : Syntax → Bool) (accept : Syntax → Bool := fun stx => !stx.hasArgs) : Option Syntax.Stack :=
  if visit root then go [] root else none
where
  go (stack : Syntax.Stack) (stx : Syntax) : Option Syntax.Stack := Id.run do
    if accept stx then
      return (stx, 0) :: stack  -- the first index is arbitrary as there is no preceding element
    for i in [0:stx.getNumArgs] do
      if visit stx[i] then
        if let some stack := go ((stx, i) :: stack) stx[i] then
          return stack
    return none

/-- Compare the `SyntaxNodeKind`s in `pattern` to those of the `Syntax`
elements in `stack`. Return `false` if `stack` is shorter than `pattern`. -/
def Stack.matches (stack : Syntax.Stack) (pattern : List $ Option SyntaxNodeKind) : Bool :=
  stack.length >= pattern.length &&
  (stack
    |>.zipWith (fun (s, _) p => p |>.map (s.isOfKind ·) |>.getD true) pattern
    |>.all id)

end Syntax

end Lean
