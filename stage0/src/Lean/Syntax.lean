/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich, Leonardo de Moura
-/
import Lean.Data.Name
import Lean.Data.Format

namespace Lean

def SourceInfo.updateTrailing (trailing : Substring) : SourceInfo → SourceInfo
  | SourceInfo.original leading pos _ endPos => SourceInfo.original leading pos trailing endPos
  | info                                     => info

/- Syntax AST -/

inductive IsNode : Syntax → Prop where
  | mk (kind : SyntaxNodeKind) (args : Array Syntax) : IsNode (Syntax.node kind args)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def unreachIsNodeMissing {β} (h : IsNode Syntax.missing) : β := False.elim (nomatch h)
def unreachIsNodeAtom {β} {info val} (h : IsNode (Syntax.atom info val)) : β := False.elim (nomatch h)
def unreachIsNodeIdent {β info rawVal val preresolved} (h : IsNode (Syntax.ident info rawVal val preresolved)) : β := False.elim (nomatch h)

namespace SyntaxNode

@[inline] def getKind (n : SyntaxNode) : SyntaxNodeKind :=
  match n with
  | ⟨Syntax.node k args, _⟩ => k
  | ⟨Syntax.missing, h⟩     => unreachIsNodeMissing h
  | ⟨Syntax.atom .., h⟩     => unreachIsNodeAtom h
  | ⟨Syntax.ident .., h⟩    => unreachIsNodeIdent h

@[inline] def withArgs {β} (n : SyntaxNode) (fn : Array Syntax → β) : β :=
  match n with
  | ⟨Syntax.node _ args, _⟩   => fn args
  | ⟨Syntax.missing, h⟩       => unreachIsNodeMissing h
  | ⟨Syntax.atom _ _, h⟩      => unreachIsNodeAtom h
  | ⟨Syntax.ident _ _ _ _, h⟩ => unreachIsNodeIdent h

@[inline] def getNumArgs (n : SyntaxNode) : Nat :=
  withArgs n $ fun args => args.size

@[inline] def getArg (n : SyntaxNode) (i : Nat) : Syntax :=
  withArgs n $ fun args => args.get! i

@[inline] def getArgs (n : SyntaxNode) : Array Syntax :=
  withArgs n $ fun args => args

@[inline] def modifyArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
  match n with
  | ⟨Syntax.node kind args, _⟩ => Syntax.node kind (fn args)
  | ⟨Syntax.missing, h⟩        => unreachIsNodeMissing h
  | ⟨Syntax.atom _ _, h⟩       => unreachIsNodeAtom h
  | ⟨Syntax.ident _ _ _ _,  h⟩ => unreachIsNodeIdent h

end SyntaxNode

namespace Syntax

def getAtomVal! : Syntax → String
  | atom _ val => val
  | _          => panic! "getAtomVal!: not an atom"

def setAtomVal : Syntax → String → Syntax
  | atom info _, v => (atom info v)
  | stx,         _ => stx

@[inline] def ifNode {β} (stx : Syntax) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
  match stx with
  | Syntax.node k args => hyes ⟨Syntax.node k args, IsNode.mk k args⟩
  | _                  => hno ()

@[inline] def ifNodeKind {β} (stx : Syntax) (kind : SyntaxNodeKind) (hyes : SyntaxNode → β) (hno : Unit → β) : β :=
  match stx with
  | Syntax.node k args => if k == kind then hyes ⟨Syntax.node k args, IsNode.mk k args⟩ else hno ()
  | _                  => hno ()

def asNode : Syntax → SyntaxNode
  | Syntax.node kind args => ⟨Syntax.node kind args, IsNode.mk kind args⟩
  | _                     => ⟨Syntax.node nullKind #[], IsNode.mk nullKind #[]⟩

def getIdAt (stx : Syntax) (i : Nat) : Name :=
  (stx.getArg i).getId

@[inline] def modifyArgs (stx : Syntax) (fn : Array Syntax → Array Syntax) : Syntax :=
  match stx with
  | node k args => node k (fn args)
  | stx         => stx

@[inline] def modifyArg (stx : Syntax) (i : Nat) (fn : Syntax → Syntax) : Syntax :=
  match stx with
  | node k args => node k (args.modify i fn)
  | stx         => stx

@[specialize] partial def replaceM {m : Type → Type} [Monad m] (fn : Syntax → m (Option Syntax)) : Syntax → m (Syntax)
  | stx@(node kind args) => do
    match (← fn stx) with
    | some stx => return stx
    | none     => return node kind (← args.mapM (replaceM fn))
  | stx => do
    let o ← fn stx
    return o.getD stx

@[specialize] partial def rewriteBottomUpM {m : Type → Type} [Monad m] (fn : Syntax → m (Syntax)) : Syntax → m (Syntax)
  | node kind args   => do
    let args ← args.mapM (rewriteBottomUpM fn)
    fn (node kind args)
  | stx => fn stx

@[inline] def rewriteBottomUp (fn : Syntax → Syntax) (stx : Syntax) : Syntax :=
  Id.run $ stx.rewriteBottomUpM fn

private def updateInfo : SourceInfo → String.Pos → String.Pos → SourceInfo
  | SourceInfo.original lead pos trail endPos, leadStart, trailStop =>
    SourceInfo.original { lead with startPos := leadStart } pos { trail with stopPos := trailStop } endPos
  | info, _, _ => info

private def chooseNiceTrailStop (trail : Substring) : String.Pos :=
trail.startPos + trail.posOf '\n'

/- Remark: the State `String.Pos` is the `SourceInfo.trailing.stopPos` of the previous token,
   or the beginning of the String. -/
@[inline]
private def updateLeadingAux : Syntax → StateM String.Pos (Option Syntax)
  | atom info@(SourceInfo.original lead _ trail _) val => do
    let trailStop := chooseNiceTrailStop trail
    let newInfo := updateInfo info (← get) trailStop
    set trailStop
    pure $ some (atom newInfo val)
  | ident info@(SourceInfo.original lead _ trail _) rawVal val pre => do
    let trailStop := chooseNiceTrailStop trail
    let newInfo := updateInfo info (← get) trailStop
    set trailStop
    pure $ some (ident newInfo rawVal val pre)
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
  | n@(Syntax.node k args)             =>
    if args.size == 0 then n
    else
     let i    := args.size - 1
     let last := updateTrailing trailing args[i]
     let args := args.set! i last;
     Syntax.node k args
  | s => s

partial def getTailWithPos : Syntax → Option Syntax
  | stx@(atom info _)   => info.getPos?.map fun _ => stx
  | stx@(ident info ..) => info.getPos?.map fun _ => stx
  | node _ args         => args.findSomeRev? getTailWithPos
  | _                   => none

open SourceInfo in
/-- Split an `ident` into its dot-separated components while preserving source info.
Macro scopes are first erased.  For example, `` `foo.bla.boo._@._hyg.4 `` ↦ `` [`foo, `bla, `boo] ``.
If `nFields` is set, we take that many fields from the end and keep the remaining components
as one name. For example, `` `foo.bla.boo `` with `(nFields := 1)` ↦ `` [`foo.bla, `boo] ``. -/
def identComponents (stx : Syntax) (nFields? : Option Nat := none) : List Syntax :=
  match stx with
  | ident (SourceInfo.original lead pos trail _) rawStr val _ =>
    let val := val.eraseMacroScopes
    -- With original info, we assume that `rawStr` represents `val`.
    let nameComps := nameComps val nFields?
    let rawComps := splitNameLit rawStr
    let rawComps :=
      if let some nFields := nFields? then
        let nPrefix := rawComps.length - nFields
        let prefixSz := rawComps.take nPrefix |>.foldl (init := 0) fun acc (ss : Substring) => acc + ss.bsize + 1
        let prefixSz := prefixSz - 1 -- The last component has no dot
        rawStr.extract 0 prefixSz :: rawComps.drop nPrefix
      else
        rawComps
    assert! nameComps.length == rawComps.length
    nameComps.zip rawComps |>.map fun (id, ss) =>
      let off := ss.startPos - rawStr.startPos
      let lead := if off == 0 then lead else "".toSubstring
      let trail := if ss.stopPos == rawStr.stopPos then trail else "".toSubstring
      let info := original lead (pos + off) trail (pos + off + ss.bsize)
      ident info ss id []
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
    let rec @[specialize] loop stx b [Inhabited (typeOf% b)] := do
      match (← f stx b) with
      | ForInStep.yield b' =>
        let mut b := b'
        if let Syntax.node k args := stx then
          if firstChoiceOnly && k == choiceKind then
            return ← loop args[0] b
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

partial def reprint (stx : Syntax) : Option String :=
  OptionM.run do
    let mut s := ""
    for stx in stx.topDown (firstChoiceOnly := true) do
      match stx with
      | atom info val           => s := s ++ reprintLeaf info val
      | ident info rawVal _ _   => s := s ++ reprintLeaf info rawVal.toString
      | node kind args          =>
        if kind == choiceKind then
          -- this visit the first arg twice, but that should hardly be a problem
          -- given that choice nodes are quite rare and small
          let s0 ← reprint args[0]
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

def hasMissing (stx : Syntax) : Bool := do
  for stx in stx.topDown do
    if stx.isMissing then
      return true
  return false

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
    { cur := t.cur.getArg idx, parents := t.parents.push $ t.cur.setArg idx arbitrary, idxs := t.idxs.push idx }
  else
    { cur := Syntax.missing, parents := t.parents.push t.cur, idxs := t.idxs.push idx }

/-- Advance to the parent of the current node, if any. -/
def up (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    let cur := if t.idxs.back < t.parents.back.getNumArgs then t.parents.back.setArg t.idxs.back t.cur else t.parents.back
    { cur := cur, parents := t.parents.pop, idxs := t.idxs.pop }
  else
    t

/-- Advance to the left sibling of the current node, if any. -/
def left (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    t.up.down (t.idxs.back - 1)
  else
    t

/-- Advance to the right sibling of the current node, if any. -/
def right (t : Traverser) : Traverser :=
  if t.parents.size > 0 then
    t.up.down (t.idxs.back + 1)
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
  st.idxs.back?.getD 0

end MonadTraverser
end Syntax

namespace SyntaxNode

@[inline] def getIdAt (n : SyntaxNode) (i : Nat) : Name :=
  (n.getArg i).getId

end SyntaxNode

def mkListNode (args : Array Syntax) : Syntax :=
  Syntax.node nullKind args

namespace Syntax

-- quotation node kinds are formed from a unique quotation name plus "quot"
def isQuot : Syntax → Bool
  | Syntax.node (Name.str _ "quot" _)         _  => true
  | Syntax.node `Lean.Parser.Term.dynamicQuot _ => true
  | _                                            => false

def getQuotContent (stx : Syntax) : Syntax :=
  if stx.isOfKind `Lean.Parser.Term.dynamicQuot then
    stx[3]
  else
    stx[1]

-- antiquotation node kinds are formed from the original node kind (if any) plus "antiquot"
def isAntiquot : Syntax → Bool
  | Syntax.node (Name.str _ "antiquot" _) _ => true
  | _                                       => false

def mkAntiquotNode (term : Syntax) (nesting := 0) (name : Option String := none) (kind := Name.anonymous) : Syntax :=
  let nesting := mkNullNode (mkArray nesting (mkAtom "$"))
  let term := match term.isIdent with
    | true  => term
    | false => mkNode `antiquotNestedExpr #[mkAtom "(", term, mkAtom ")"]
  let name := match name with
    | some name => mkNode `antiquotName #[mkAtom ":", mkAtom name]
    | none      => mkNullNode
  mkNode (kind ++ `antiquot) #[mkAtom "$", nesting, term, name]

-- Antiquotations can be escaped as in `$$x`, which is useful for nesting macros. Also works for antiquotation splices.
def isEscapedAntiquot (stx : Syntax) : Bool :=
  !stx[1].getArgs.isEmpty

-- Also works for antiquotation splices.
def unescapeAntiquot (stx : Syntax) : Syntax :=
  if isAntiquot stx then
    stx.setArg 1 $ mkNullNode stx[1].getArgs.pop
  else
    stx

-- Also works for token antiquotations.
def getAntiquotTerm (stx : Syntax) : Syntax :=
  let e := if stx.isAntiquot then stx[2] else stx[3]
  if e.isIdent then e
  else
    -- `e` is from `"(" >> termParser >> ")"`
    e[1]

def antiquotKind? : Syntax → Option SyntaxNodeKind
  | Syntax.node (Name.str k "antiquot" _) args =>
    if args[3].isOfKind `antiquotName then some k
    else
      -- we treat all antiquotations where the kind was left implicit (`$e`) the same (see `elimAntiquotChoices`)
      some Name.anonymous
  | _                                          => none

-- An "antiquotation splice" is something like `$[...]?` or `$[...]*`.
def antiquotSpliceKind? : Syntax → Option SyntaxNodeKind
  | Syntax.node (Name.str k "antiquot_scope" _) args => some k
  | _                                                => none

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
  | Syntax.node (Name.str k "antiquot_suffix_splice" _) args => some k
  | _                                                        => none

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

end Syntax
end Lean
