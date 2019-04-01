import init.lean.name

open Lean (Name)

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

instance : HasBeq SyntaxNodeKind :=
⟨λ k₁ k₂, k₁.id == k₂.id⟩

def nextKind (name : Name) : IO SyntaxNodeKind :=
do id ← nextUniqId.get,
   nextUniqId.set (id+1),
   pure { name := name, id := id }

inductive Syntax
| missing
| node   (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes)
| atom   (info : Option SourceInfo) (val : String)
| ident  (info : Option SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Name) (scopes : MacroScopes)

instance : Inhabited Syntax :=
⟨Syntax.missing⟩

inductive IsNode : Syntax → Prop
| mk (kind : SyntaxNodeKind) (args : Array Syntax) (scopes : MacroScopes) : IsNode (Syntax.node kind args scopes)

def SyntaxNode : Type := {s : Syntax // IsNode s }

def notIsNodeMissing (h : IsNode Syntax.missing) : False                    := match h with end
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

def mkNotKind : IO SyntaxNodeKind := nextKind `not
@[init mkNotKind] constant notKind : SyntaxNodeKind := default _
def mkIfKind : IO SyntaxNodeKind  := nextKind `if
@[init mkIfKind] constant ifKind  : SyntaxNodeKind := default _

@[inline] def mkAtom (val : String) : Syntax :=
Syntax.atom none val

@[inline] def mkNotAux (tk : Syntax) (c : Syntax) : Syntax :=
Syntax.node notKind [tk, c].toArray []

@[inline] def mkNot (c : Syntax) : Syntax :=
mkNotAux (mkAtom "not") c

@[inline] def withNot {α : Type} (n : SyntaxNode) (fn : Syntax → α) : α :=
match n with
| ⟨Syntax.node _ args _, _⟩   := fn (args.get 1)
| ⟨Syntax.missing, h⟩         := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩        := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩ := unreachIsNodeIdent h

@[inline] def isNot {α : Type} (n : Syntax) (base : α) (fn : Syntax → α)  : α :=
match n with
| Syntax.node k args _   := if k == notKind then fn (args.get 1) else base
| Syntax.missing         := base
| Syntax.atom _ _        := base
| Syntax.ident _ _ _ _ _ := base

@[inline] def updateNot (src : SyntaxNode) (c : Syntax) : Syntax :=
match src with
| ⟨Syntax.node kind args scopes, _⟩ := Syntax.node kind (args.set 1 c) scopes
| ⟨Syntax.missing, h⟩               := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩              := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩       := unreachIsNodeIdent h

@[inline] def mkIfAux (ifTk : Syntax) (condNode : Syntax) (thenTk : Syntax) (thenNode : Syntax) (elseTk : Syntax) (elseNode: Syntax) : Syntax :=
Syntax.node ifKind [ifTk, condNode, thenTk, thenNode, elseTk, elseNode].toArray []

@[inline] def mkIf (c t e : Syntax) : Syntax :=
mkIfAux (mkAtom "if") c (mkAtom "then") t (mkAtom "else") e

@[inline] def withIf {α : Type} (src : SyntaxNode) (fn : Syntax → Syntax → Syntax → α) : α :=
match src with
| ⟨Syntax.node _ args _, _⟩    := fn (args.get 1) (args.get 3) (args.get 5)
| ⟨Syntax.missing, h⟩          := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩         := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩  := unreachIsNodeIdent h

@[inline] def updateIf (src : SyntaxNode) (c t e : Syntax) : Syntax :=
match src with
| ⟨Syntax.node kind args scopes, _⟩ :=
  let args := args.set 1 c in
  let args := args.set 3 t in
  let args := args.set 5 e in
  Syntax.node kind args scopes
| ⟨Syntax.missing, h⟩               := unreachIsNodeMissing h
| ⟨Syntax.atom _ _, h⟩              := unreachIsNodeAtom h
| ⟨Syntax.ident _ _ _ _ _, h⟩       := unreachIsNodeIdent h

abbrev FrontendConfig := Bool   -- placeholder
abbrev Message        := String -- placeholder
abbrev TransformM     := ReaderT FrontendConfig $ ExceptT Message Id
abbrev Transformer    := SyntaxNode → TransformM (Option Syntax)

set_option pp.implicit true
set_option trace.compiler.boxed true

def flipIf : Transformer :=
λ n, withIf n $ λ c t e,
 isNot c (pure n.val) $ λ c',
 pure (updateIf n c' e t)

/-
The generated code can be still be improved if we modify ExceptT using the trick described in
our paper.
-/
