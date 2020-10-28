import init.lean.name

open Lean (Name NameMap)

def MacroScope := Nat
abbrev MacroScopes := List MacroScope

structure SourceInfo :=
(leading  : Substring)
(pos      : Nat)
(trailing : Substring)

def mkUniqIdRef : IO (IO.Ref Nat) :=
IO.mkRef 0

@[init mkUniqIdRef]
constant nextUniqId : IO.Ref Nat := default _

structure SyntaxNodeKind :=
(name : Name) (id : Nat)

instance : Inhabited SyntaxNodeKind :=
⟨{name := default _, id := default _}⟩

instance : BEq SyntaxNodeKind :=
⟨λ k₁ k₂, k₁.id == k₂.id⟩

def mkNameToKindTable : IO (IO.Ref (NameMap Nat)) :=
IO.mkRef {}

@[init mkNameToKindTable]
constant nameToKindTable : IO.Ref (NameMap Nat) := default _

def nextKind (k : Name) : IO SyntaxNodeKind :=
do m ← nameToKindTable.get,
   when (m.contains k) (throw $ IO.userError ("Error kind '" ++ toString k ++ "' already exists")),
   id ← nextUniqId.get,
   nameToKindTable.set (m.insert k id),
   nextUniqId.set (id+1),
   pure { name := k, id := id }

def mkNullKind : IO SyntaxNodeKind := nextKind `null
@[init mkNullKind] constant nullKind : SyntaxNodeKind := default _

inductive Syntax
| missing
| node   (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes)
| atom   (info : Option SourceInfo) (val : String)
| ident  (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Name) (scopes : MacroScopes)

instance : Inhabited Syntax :=
⟨Syntax.missing⟩

def SyntaxNodeKind.fix : SyntaxNodeKind → IO SyntaxNodeKind
| {name := n, ..} := do
  m ← nameToKindTable.get,
  match m.find n with
  | some id := pure {name := n, id := id}
  | none    := throw $ IO.userError ("Error unknown Syntax kind '" ++ toString n ++ "'")

partial def Syntax.fixKinds : Syntax → IO Syntax
| (Syntax.node k args scopes) := do
  k ← k.fix,
  args ← args.mmap Syntax.fixKinds,
  pure (Syntax.node k args scopes)
| other                       := pure other

inductive IsNode : Syntax → Prop
| mk (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes) : IsNode (Syntax.node kind args scopes)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def notIsNodeMissing (h : IsNode Syntax.missing) : False                   := match h with end
def notIsNodeAtom   {info val} (h : IsNode (Syntax.atom info val)) : False := match h with end
def notIsNodeIdent  {info rawVal val preresolved scopes} (h : IsNode (Syntax.ident info rawVal val preresolved scopes)) : False := match h with end

def unreachIsNodeMissing {α : Type} (h : IsNode Syntax.missing) : α := False.elim (notIsNodeMissing h)
def unreachIsNodeAtom {α : Type} {info val} (h : IsNode (Syntax.atom info val)) : α := False.elim (notIsNodeAtom h)
def unreachIsNodeIdent {α : Type} {info rawVal val preresolved scopes} (h : IsNode (Syntax.ident info rawVal val preresolved scopes)) : α := False.elim (match h with end)

@[inline] def toSyntaxNode {α : Type} (s : Syntax) (base : α) (fn : SyntaxNode → α) : α :=
match s with
| Syntax.node kind args scopes := fn ⟨Syntax.node kind args scopes, IsNode.mk kind args scopes⟩
| other := base

@[inline] def toSyntaxNodeOf {α : Type} (kind : SyntaxNodeKind) (s : Syntax) (base : α) (fn : SyntaxNode → α) : α :=
match s with
| Syntax.node k args scopes :=
  if k == kind then fn ⟨Syntax.node kind args scopes, IsNode.mk kind args scopes⟩
  else base
| other := base

@[inline] def mkAtom (val : String) : Syntax :=
Syntax.atom none val

def mkOptionSomeKind : IO SyntaxNodeKind := nextKind `some
@[init mkOptionSomeKind] constant optionSomeKind : SyntaxNodeKind := default _
def mkOptionNoneKind : IO SyntaxNodeKind := nextKind `none
@[init mkOptionSomeKind] constant optionNoneKind : SyntaxNodeKind := default _
def mkManyKind : IO SyntaxNodeKind := nextKind `many
@[init mkManyKind] constant manyKind : SyntaxNodeKind := default _
def mkHoleKind : IO SyntaxNodeKind := nextKind `hole
@[init mkHoleKind] constant holeKind : SyntaxNodeKind := default _
def mkNotKind : IO SyntaxNodeKind := nextKind `not
@[init mkNotKind] constant notKind : SyntaxNodeKind := default _
def mkIfKind : IO SyntaxNodeKind  := nextKind `if
@[init mkIfKind] constant ifKind  : SyntaxNodeKind := default _
def mkLetKind : IO SyntaxNodeKind  := nextKind `let
@[init mkLetKind] constant letKind  : SyntaxNodeKind := default _
def mkLetLhsIdKind : IO SyntaxNodeKind  := nextKind `letLhsId
@[init mkLetLhsIdKind] constant letLhsIdKind : SyntaxNodeKind := default _
def mkLetLhsPatternKind : IO SyntaxNodeKind  := nextKind `letLhsPattern
@[init mkLetLhsPatternKind] constant letLhsPatternKind  : SyntaxNodeKind := default _

@[inline] def withArgs {α : Type} (n : SyntaxNode) (fn : Array Syntax → α) : α :=
match n with
| ⟨Syntax.node _ args _, _⟩   := fn args
| ⟨Syntax.missing, h⟩         := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩        := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩ := unreachIsNodeIdent h

@[inline] def updateArgs (n : SyntaxNode) (fn : Array Syntax → Array Syntax) : Syntax :=
match n with
| ⟨Syntax.node kind args scopes, _⟩ := Syntax.node kind (fn args) scopes
| ⟨Syntax.missing, h⟩               := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩              := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩       := unreachIsNodeIdent h

@[inline] def mkNotAux (tk : Syntax) (c : Syntax) : Syntax :=
Syntax.node notKind [tk, c].toArray []

@[inline] def mkNot (c : Syntax) : Syntax :=
mkNotAux (mkAtom "not") c

@[inline] def withNot {α : Type} (n : SyntaxNode) (fn : Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 1)

@[inline] def updateNot (src : SyntaxNode) (c : Syntax) : Syntax :=
updateArgs src $ λ args, args.set 1 c

@[inline] def mkIfAux (ifTk : Syntax) (condNode : Syntax) (thenTk : Syntax) (thenNode : Syntax) (elseTk : Syntax) (elseNode: Syntax) : Syntax :=
Syntax.node ifKind [ifTk, condNode, thenTk, thenNode, elseTk, elseNode].toArray []

@[inline] def mkIf (c t e : Syntax) : Syntax :=
mkIfAux (mkAtom "if") c (mkAtom "then") t (mkAtom "else") e

@[inline] def withIf {α : Type} (n : SyntaxNode) (fn : Syntax → Syntax → Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 1) (args.get 3) (args.get 5)

@[inline] def updateIf (src : SyntaxNode) (c t e : Syntax) : Syntax :=
updateArgs src $ λ args,
  let args := args.set 1 c in
  let args := args.set 3 t in
  let args := args.set 5 e in
  args

@[inline] def mkLetAux (letTk : Syntax) (lhs : Syntax) (assignTk : Syntax) (val : Syntax) (inTk : Syntax) (body : Syntax) : Syntax :=
Syntax.node letKind [letTk, lhs, assignTk, val, inTk, body].toArray []

@[inline] def mkLet (lhs : Syntax) (val : Syntax) (body : Syntax) : Syntax :=
mkLetAux (mkAtom "let") lhs (mkAtom ":=") val (mkAtom "in") body

@[inline] def withLet {α : Type} (n : SyntaxNode) (fn : Syntax → Syntax → Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 1) (args.get 3) (args.get 5)

@[inline] def updateLet (src : SyntaxNode) (lhs val body : Syntax) : Syntax :=
updateArgs src $ λ args,
  let args := args.set 1 lhs in
  let args := args.set 3 val in
  let args := args.set 5 body in
  args

@[inline] def mkLetLhsId (id : Syntax) (binders : Syntax) (type : Syntax) : Syntax :=
Syntax.node letLhsIdKind [id, binders, type].toArray []

@[inline] def withLetLhsId {α : Type} (n : SyntaxNode) (fn : Syntax → Syntax → Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 0) (args.get 1) (args.get 2)

@[inline] def updateLhsId (src : SyntaxNode) (id binders type : Syntax) : Syntax :=
updateArgs src $ λ args,
  let args := args.set 0 id in
  let args := args.set 1 binders in
  let args := args.set 2 type in
  args

@[inline] def mkLetLhsPattern (pattern : Syntax) : Syntax :=
Syntax.node letLhsPatternKind [pattern].toArray []

@[inline] def withLetLhsPattern {α : Type} (n : SyntaxNode) (fn : Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 0)

@[inline] def withOptionSome {α : Type} (n : SyntaxNode) (fn : Syntax → α) : α :=
withArgs n $ λ args, fn (args.get 0)

def Syntax.getNumChildren (n : Syntax) : Nat :=
match n with
| Syntax.node _ args _ := args.size
| _                    := 0

def hole : Syntax := Syntax.node holeKind ∅ []

def mkOptionSome (s : Syntax) := Syntax.node optionSomeKind [s].toArray []

abbrev FrontendConfig := Bool   -- placeholder
abbrev Message        := String -- placeholder
abbrev TransformM     := ReaderT FrontendConfig $ ExceptT Message Id
abbrev Transformer    := SyntaxNode → TransformM (Option Syntax)

def noExpansion : TransformM (Option Syntax) := pure none

@[inline] def Syntax.case {α : Type} (n : Syntax) (k : SyntaxNodeKind) (fn : SyntaxNode → TransformM (Option α)) : TransformM (Option α) :=
match n with
| Syntax.node k' args s := if k == k' then fn ⟨Syntax.node k' args s, IsNode.mk _ _ _⟩ else pure none
| _                     := pure none

@[inline] def TransformM.orCase {α : Type} (x y : TransformM (Option α)) : TransformM (Option α) :=
λ cfg, match x cfg with
 | Except.ok none := y cfg
 | other          := other

infix `<?>`:2 := TransformM.orCase

set_option pp.implicit true
set_option trace.compiler.boxed true

def flipIf : Transformer :=
λ n, withIf n $ λ c t e,
  c.case notKind $ λ c, withNot c $ λ c',
    pure $ updateIf n c' e t

def letTransformer : Transformer :=
λ n, withLet n $ λ lhs val body,
 (lhs.case letLhsIdKind $ λ lhs, withLetLhsId lhs $ λ id binders type,
   if binders.getNumChildren == 0 then
     type.case optionNoneKind $ λ _,
       let newLhs := updateLhsId lhs id binders (mkOptionSome hole) in
       pure (some (updateLet n newLhs val body))
   else
     -- TODO
     noExpansion)
 <?>
 (lhs.case letLhsPatternKind $ λ lhs,
   -- TODO
   noExpansion)

@[inline] def Syntax.isNode {α : Type} (n : Syntax) (fn : SyntaxNodeKind → SyntaxNode → TransformM (Option α)) : TransformM (Option α) :=
match n with
| Syntax.node k args s := fn k ⟨Syntax.node k args s, IsNode.mk _ _ _⟩
| other                := pure none

/- Version without using the combinator <?>. -/
def letTransformer' : Transformer :=
  λ n, withLet n $ λ lhs val body,
  lhs.isNode $ λ k lhs, -- lhs is now a SyntaxNode
  if k == letLhsIdKind then withLetLhsId lhs $ λ id binders type,
    if binders.getNumChildren == 0 then
      type.case optionNoneKind $ λ _,
        let newLhs := updateLhsId lhs id binders (mkOptionSome hole) in
        pure (some (updateLet n newLhs val body))
    else
      -- TODO
      noExpansion
  else withLetLhsPattern lhs $ λ pattern,
    -- TODO
    noExpansion
