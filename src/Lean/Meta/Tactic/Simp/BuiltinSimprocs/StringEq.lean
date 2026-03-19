/-
Copyright (c) 2026 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
import Init.Data.String.SimpEq
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.FindPos
import Init.While

namespace String

open Lean Meta
open Internal.SimpEq

inductive ExprType where
  | string
  | list
  | char
deriving DecidableEq

-- Regarding erased parts: erased parts indicate what has been cancelled out in the
-- `cancelLeft` / `cancelRight` procedures; we treat the like `anyXYZ` but don't allow them
-- to be cancelled again (see `isDefEq` / `isCompatibleWith`)
inductive ExprStructure : ExprType → Type where
  -- String
  | stringAppend (a b : ExprStructure .string) : ExprStructure .string
  | push (s : ExprStructure .string) (c : ExprStructure .char) : ExprStructure .string
  | singleton (c : ExprStructure .char) : ExprStructure .string
  | ofList (l : ExprStructure .list) : ExprStructure .string
  /--
  `s.str.sliceTo s.startInclusive` and `s.str.sliceFrom s.endExclusive` are erased but still part
  of the original expression
  -/
  | stringLit (s : String.Slice) : ExprStructure .string
  | anyString (s : Expr) : ExprStructure .string
  | erasedString (s : Expr) : ExprStructure .string
  -- List Char
  | nil : ExprStructure .list
  | cons (c : ExprStructure .char) (l : ExprStructure .list) : ExprStructure .list
  | listAppend (a b : ExprStructure .list) : ExprStructure .list
  | toList (s : ExprStructure .string) : ExprStructure .list
  | anyList (l : Expr) : ExprStructure .list
  | erasedList (l : Expr) : ExprStructure .list
  -- Char
  | charLit (c : Char) : ExprStructure .char
  | anyChar (c : Expr) : ExprStructure .char
  | erasedChar (c : Expr) : ExprStructure .char

-- TODO: make this a computed field (private inductives can't have computed fields???)
def ExprStructure.maxDepth : ExprStructure ty → Nat
  -- String
  | .stringAppend a b => max a.maxDepth b.maxDepth + 1
  | .push s _ => s.maxDepth + 1
  | .singleton _ => 0
  | .ofList l => l.maxDepth + 1
  | .stringLit _ => 0
  | .anyString _ => 0
  | .erasedString _ => 0
  -- List Char
  | .nil => 0
  | .cons _ l => l.maxDepth + 1
  | .listAppend a b => max a.maxDepth b.maxDepth + 1
  | .toList s => s.maxDepth + 1
  | .anyList _ => 0
  | .erasedList _ => 0
  -- Char
  | .charLit _ => 0
  | .anyChar _ => 0
  | .erasedChar _ => 0

-- TODO: make this a computed field (private inductives can't have computed fields???)
def ExprStructure.isEmpty : ExprStructure ty → Bool
  -- String
  | .stringAppend a b => a.isEmpty && b.isEmpty
  | .push _ _ => false
  | .singleton _ => false
  | .ofList l => l.isEmpty
  | .stringLit s => s.str.isEmpty
  | .anyString _ => false
  | .erasedString _=> false
  -- List Char
  | .nil => true
  | .cons _ _ => false
  | .listAppend a b => a.isEmpty && b.isEmpty
  | .toList s => s.isEmpty
  | .anyList _ => false
  | .erasedList _=> false
  -- Char
  | .charLit _ => false
  | .anyChar _ => false
  | .erasedChar _=> false

def ExprStructure.allErased : ExprStructure ty → Bool
  -- String
  | .stringAppend a b => a.allErased && b.allErased
  | .push s c => s.allErased && c.allErased
  | .singleton c => c.allErased
  | .ofList l => l.allErased
  | .stringLit s => s.isEmpty
  | .anyString _ => false
  | .erasedString _=> true
  -- List Char
  | .nil => true
  | .cons c l => c.allErased && l.allErased
  | .listAppend a b => a.allErased && b.allErased
  | .toList s => s.allErased
  | .anyList _ => false
  | .erasedList _=> true
  -- Char
  | .charLit _ => false
  | .anyChar _ => false
  | .erasedChar _=> true

def listAppendInst : Expr :=
  mkApp2 (.const ``instHAppendOfAppend [0]) (.app (.const ``List [0]) (mkConst ``Char))
    (.app (.const ``List.instAppend [0]) (mkConst ``Char))

def stringAppendInst : Expr :=
  mkApp2 (.const ``instHAppendOfAppend [0]) (mkConst ``String) (mkConst ``instAppendString)

@[match_pattern]
def mkCharLit (n : Nat) : Expr :=
  .app (.const ``Char.ofNat []) (mkRawNatLit n)

mutual

partial def createStringStructure (e : Expr) : MetaM (ExprStructure .string) := do
  let e' ← whnf e
  if let mkStrLit s := e' then
    return .stringLit s
  match_expr e' with
  | String.push s c => return .push (← createStringStructure s) (← createCharStructure c)
  | String.singleton c => return .singleton (← createCharStructure c)
  | String.ofList l => return .ofList (← createListStructure l)
  | HAppend.hAppend _ _ _ inst a b =>
    if ← pure (inst == stringAppendInst) <||> isDefEqI inst stringAppendInst then
      return .stringAppend (← createStringStructure a) (← createStringStructure b)
    return .anyString e
  | _ => return .anyString e

partial def createListStructure (e : Expr) : MetaM (ExprStructure .list) := do
  let e' ← whnf e
  match_expr e' with
  | List.nil _ => return .nil
  | List.cons _ c l => return .cons (← createCharStructure c) (← createListStructure l)
  | String.toList s => return .toList (← createStringStructure s)
  | HAppend.hAppend _ _ _ inst a b =>
    if ← pure (inst == listAppendInst) <||> isDefEqI inst listAppendInst then
      return .listAppend (← createListStructure a) (← createListStructure b)
    return .anyList e
  | _ => return .anyList e

partial def createCharStructure (e : Expr) : MetaM (ExprStructure .char) := do
  let e' ← whnf e
  match e' with
  | mkCharLit n => return .charLit (Char.ofNat n)
  | _ => return .anyChar e

end

protected def ExprStructure.toExpr : ExprStructure ty → Expr
  -- String
  | .stringAppend a b =>
    let stringAppend := mkApp4 (.const ``HAppend.hAppend [0, 0, 0])
      (mkConst ``String) (mkConst ``String) (mkConst ``String) stringAppendInst
    mkApp2 stringAppend a.toExpr b.toExpr
  | .push s c => mkApp2 (mkConst ``String.push) s.toExpr c.toExpr
  | .singleton c => .app (mkConst ``String.singleton) c.toExpr
  | .ofList l => .app (mkConst ``String.ofList) l.toExpr
  | .stringLit s => mkStrLit s.str
  | .anyString s => s
  | .erasedString s => s
  -- List Char
  | .nil => .app (.const ``List.nil [0]) (mkConst ``Char)
  | .cons c l =>
    let cons := .app (.const ``List.cons [0]) (mkConst ``Char)
    mkApp2 cons c.toExpr l.toExpr
  | .listAppend a b =>
    let listAppend :=  mkApp4 (.const ``HAppend.hAppend [0, 0, 0])
      (.app (.const ``List [0]) (mkConst ``Char)) (.app (.const ``List [0]) (mkConst ``Char))
      (.app (.const ``List [0]) (mkConst ``Char)) listAppendInst
    mkApp2 listAppend a.toExpr b.toExpr
  | .toList s => .app (mkConst ``String.toList) s.toExpr
  | .anyList l => l
  | .erasedList l => l
  -- Char
  | .charLit c => mkCharLit c.toNat
  | .anyChar c => c
  | .erasedChar c => c

protected def ExprStructure.toStructExpr : ExprStructure ty → Expr
  -- String
  | .stringAppend a b => mkApp2 (mkConst ``StringStructure.append) a.toStructExpr b.toStructExpr
  | .push s c => mkApp2 (mkConst ``StringStructure.push) s.toStructExpr c.toStructExpr
  | .singleton c => .app (mkConst ``StringStructure.singleton) c.toStructExpr
  | .ofList l => .app (mkConst ``StringStructure.ofList) l.toStructExpr
  | .stringLit s => .app (mkConst ``StringStructure.lit) (ToExpr.toExpr s.str.toList)
  | .anyString s => .app (mkConst ``StringStructure.any) s
  | .erasedString s => .app (mkConst ``StringStructure.any) s
  -- List Char
  | .nil => mkConst ``ListStructure.nil
  | .cons c l => mkApp2 (mkConst ``ListStructure.cons) c.toStructExpr l.toStructExpr
  | .listAppend a b => mkApp2 (mkConst ``ListStructure.append) a.toStructExpr b.toStructExpr
  | .toList s => .app (mkConst ``ListStructure.toList) s.toStructExpr
  | .anyList l => .app (mkConst ``ListStructure.any) l
  | .erasedList l => .app (mkConst ``ListStructure.any) l
  -- Char
  | .charLit c => mkCharLit c.toNat
  | .anyChar c => c
  | .erasedChar c => c

/--
Returns true iff both structures are definitionally equivalent and don't contain any erased parts.
-/
protected def ExprStructure.isDefEq : ExprStructure ty → ExprStructure ty → MetaM Bool
  -- String
  | .stringAppend a b, .stringAppend a' b' => a.isDefEq a' <&&> b.isDefEq b'
  | .push s c, .push s' c' => s.isDefEq s' <&&> c.isDefEq c'
  | .singleton c, .singleton c' => c.isDefEq c'
  | .ofList l, .ofList l' => l.isDefEq l'
  | .stringLit s, .stringLit s' => pure (s == s')
  | .anyString s, .anyString s' => isDefEq s s'
  -- List Char
  | .nil, .nil => pure true
  | .cons c l, .cons c' l' => c.isDefEq c' <&&> l.isDefEq l'
  | .listAppend a b, .listAppend a' b' => a.isDefEq a' <&&> b.isDefEq b'
  | .toList s, .toList s' => s.isDefEq s'
  | .anyList l, .anyList l' => isDefEq l l'
  -- Char
  | .charLit c, .charLit c' => pure (c == c')
  | .anyChar c, .anyChar c' => isDefEq c c'
  -- We don't want to erase any already erased parts
  -- and thus make `isDefEq` irreflexive for `erasedString` / `erasedList` / `erasedChar`
  | _, _ => pure false

/--
Returns true iff both structures are definitionally equivalent or both characters and don't contain
any erased parts.
-/
protected def ExprStructure.isCompatibleWith
    (a : ExprStructure ty) (b : ExprStructure ty') : MetaM (Option (PLift (ty = ty'))) := do
  if h : ty = ty' then
    if ty matches .char then
      if a matches .erasedChar _ || b matches .erasedChar _ then
        pure none
      else
        pure (some ⟨h⟩)
    else if ← a.isDefEq (h ▸ b) then
      pure (some ⟨h⟩)
    else
      pure none
  else pure none

def ExprStructure.toAny (x : ExprStructure ty) : ExprStructure ty :=
  match ty with
  | .string => .anyString x.toExpr
  | .list => .anyList x.toExpr
  | .char => .anyChar x.toExpr

inductive ErasureResult (ty : ExprType) where
  | empty
  | noErased
  | result (erased unerased : ExprStructure ty)

@[inline]
def ErasureResult.erasedValueD (x : ErasureResult ty) (default : ExprStructure ty) :
    ExprStructure ty :=
  match x with
  | .result x _ => x
  | .noErased => default.toAny
  | .empty => default

@[inline]
def ErasureResult.unerasedValueD (x : ErasureResult ty) (default : ExprStructure ty) :
    ExprStructure ty :=
  match x with
  | .result _ x => x
  | .noErased => default.toAny
  | _ => default

@[inline]
def ErasureResult.withErased (x : ErasureResult ty) (val : ExprStructure ty) :
    ErasureResult ty :=
  match x with
  | .noErased => .result val.toAny val.toAny
  | x => x

@[inline]
def ErasureResult.map (f : ExprStructure ty → ExprStructure ty') :
    ErasureResult ty → ErasureResult ty'
  | .empty => .empty
  | .noErased => .noErased
  | .result x y => .result (f x) (f y)

@[specialize]
def ErasureResult.map₂
    (f : ExprStructure ty → ExprStructure ty' → ExprStructure ty'')
    (lonly : ExprStructure ty → ExprStructure ty'')
    (ronly : ExprStructure ty' → ExprStructure ty'')
    (l : ExprStructure ty) (r : ExprStructure ty') :
    ErasureResult ty → ErasureResult ty' → ErasureResult ty''
  | .empty, .empty => .empty
  | .empty, .noErased => .result (ronly r.toAny) (f l r.toAny)
  | .empty, .result x y => .result (ronly x) (f l y)
  | .noErased, .empty => .result (lonly l.toAny) (f l.toAny r)
  | .noErased, .noErased => .noErased
  | .noErased, .result x y => .result (f l.toAny x) (f l.toAny y)
  | .result x y, .empty => .result (lonly x) (f y r)
  | .result x y, .noErased => .result (f x r.toAny) (f y r.toAny)
  | .result x y, .result x' y' => .result (f x x') (f y y')

--set_option trace.compiler.ir.result true in
def ExprStructure.removeErased : ExprStructure ty → ErasureResult ty
  -- String
  | .stringAppend a b => .map₂ .stringAppend id id a b a.removeErased b.removeErased
  | .push s c => .map₂ .push id .singleton s c s.removeErased c.removeErased
  | .singleton c => c.removeErased.map .singleton
  | .ofList l => l.removeErased.map .ofList
  | .stringLit s =>
    if s.startInclusive = s.str.startPos ∧ s.endExclusive = s.str.endPos then
      .noErased
    else if s.isEmpty then
      .empty
    else
      .result (.stringLit s.copy) (.stringLit s)
  | .anyString _ => .noErased
  | .erasedString _ => .empty
  -- List Char
  | .nil => .noErased
  | .cons c l => .map₂ .cons (.cons · .nil) id c l c.removeErased
    (if l matches .nil then .empty else l.removeErased)
  | .listAppend a b => .map₂ .listAppend id id a b a.removeErased b.removeErased
  | .toList l => l.removeErased.map .toList
  | .anyList _ => .noErased
  | .erasedList _ => .empty
  -- Char
  | .charLit _ => .noErased
  | .anyChar _ => .noErased
  | .erasedChar _ => .empty

def ExprStructure.removeErasedTop (e : ExprStructure .string) :
    ExprStructure .string × ExprStructure .string :=
  match e.removeErased with
  | .empty => (.stringLit "", e)
  | .noErased => (e.toAny, e.toAny)
  | .result x y => (x, y)

def ExprStructure.unerase : ExprStructure ty → ExprStructure ty
  -- String
  | .stringAppend a b => .stringAppend a.unerase b.unerase
  | .push s c => .push s.unerase c.unerase
  | .singleton c => .singleton c.unerase
  | .ofList l => .ofList l.unerase
  | .stringLit s => .stringLit s.str.toSlice
  | .anyString s => .anyString s
  | .erasedString s => .anyString s
  -- List Char
  | .nil => .nil
  | .cons c l => .cons c.unerase l.unerase
  | .listAppend a b => .listAppend a.unerase b.unerase
  | .toList l => .toList l.unerase
  | .anyList l => .anyList l
  | .erasedList l => .anyList l
  -- Char
  | .charLit c => .charLit c
  | .anyChar c => .anyChar c
  | .erasedChar c => .anyChar c

inductive CancelElement where
  | cons (l r : Expr)
  | string (e : Expr)
  | list (e : Expr)
  | char (e : Expr)
deriving Repr

def cancelElementsToStructExpr (as : Array CancelElement) : Expr :=
  as.foldr (init := mkConst ``Cancellation.nil) fun
    | .cons l r, s => mkApp3 (mkConst ``Cancellation.cons) l r s
    | .string e, s => mkApp2 (mkConst ``Cancellation.string) e s
    | .list e, s => mkApp2 (mkConst ``Cancellation.list) e s
    | .char e, s => mkApp2 (mkConst ``Cancellation.char) e s

inductive Path : ExprType → Type where
  | root : Path .string
  | stringAppendLeft (parent : Path .string) (right : ExprStructure .string) : Path .string
  | stringAppendRight (parent : Path .string) (left : ExprStructure .string) : Path .string
  | push (parent : Path .string) (c : ExprStructure .char) : Path .string
  | toList (parent : Path .list) : Path .string

  | cons (parent : Path .list) (c : ExprStructure .char) : Path .list
  | listAppendLeft (parent : Path .list) (right : ExprStructure .list) : Path .list
  | listAppendRight (parent : Path .list) (left : ExprStructure .list) : Path .list
  | ofList (parent : Path .string) : Path .list

  | singletonChar (parent : Path .string) : Path .char
  | pushChar (parent : Path .string) (s : ExprStructure .string) : Path .char
  | consChar (parent : Path .list) (l : ExprStructure .list) : Path .char
  | litChar (parent : Path .string) (s : String.Slice) (p : s.str.Pos)
    (h : p ≠ s.str.endPos) : Path .char

def ExprStructure.litChar (s : String.Slice) (p : s.str.Pos) (h : p ≠ s.str.endPos) :
    ExprStructure .char :=
  if s.startInclusive ≤ p ∧ p < s.endExclusive then
    .charLit (p.get h)
  else
    .erasedChar (mkCharLit (p.get h).toNat)

/-- Depth-first expression tree traverser -/
@[unbox]
structure Traverser where
  {type : ExprType}
  path : Path type
  expr : ExprStructure type

def Traverser.root (e : ExprStructure .string) : Traverser := ⟨.root, e⟩

def Path.toStruct : Path ty → ExprStructure ty → ExprStructure .string
  | .root, e => e
  -- String
  | .stringAppendLeft parent right, left => parent.toStruct (.stringAppend left right)
  | .stringAppendRight parent left, right => parent.toStruct (.stringAppend left right)
  | .push parent c, s => parent.toStruct (.push s c)
  | .toList parent, s => parent.toStruct (.toList s)
  -- List Char
  | .cons parent c, l => parent.toStruct (.cons c l)
  | .listAppendLeft parent right, left => parent.toStruct (.listAppend left right)
  | .listAppendRight parent left, right => parent.toStruct (.listAppend left right)
  | .ofList parent, l => parent.toStruct (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.toStruct (.singleton c)
  | .pushChar parent s, c => parent.toStruct (.push s c)
  | .consChar parent l, c => parent.toStruct (.cons c l)
  | .litChar parent s _ _, _ => parent.toStruct (.stringLit s)

def Path.toStructUnerasePrefix : Path ty → ExprStructure ty → ExprStructure .string
  | .root, e => e
  -- String
  | .stringAppendLeft parent right, left => parent.toStructUnerasePrefix (.stringAppend left right)
  | .stringAppendRight parent left, right => parent.toStructUnerasePrefix (.stringAppend left.unerase right)
  | .push parent c, s => parent.toStructUnerasePrefix (.push s c)
  | .toList parent, s => parent.toStructUnerasePrefix (.toList s)
  -- List Char
  | .cons parent c, l => parent.toStructUnerasePrefix (.cons c.unerase l)
  | .listAppendLeft parent right, left => parent.toStructUnerasePrefix (.listAppend left right)
  | .listAppendRight parent left, right => parent.toStructUnerasePrefix (.listAppend left.unerase right)
  | .ofList parent, l => parent.toStructUnerasePrefix (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.toStructUnerasePrefix (.singleton c)
  | .pushChar parent s, c => parent.toStructUnerasePrefix (.push s.unerase c)
  | .consChar parent l, c => parent.toStructUnerasePrefix (.cons c l)
  | .litChar parent s _ _, _ =>
    parent.toStructUnerasePrefix
      (.stringLit { s with
        startInclusive := s.str.startPos, startInclusive_le_endExclusive := by simp })

def Path.toStructUneraseSuffix : Path ty → ExprStructure ty → ExprStructure .string
  | .root, e => e
  -- String
  | .stringAppendLeft parent right, left => parent.toStructUneraseSuffix (.stringAppend left right.unerase)
  | .stringAppendRight parent left, right => parent.toStructUneraseSuffix (.stringAppend left right)
  | .push parent c, s => parent.toStructUneraseSuffix (.push s c.unerase)
  | .toList parent, s => parent.toStructUneraseSuffix (.toList s)
  -- List Char
  | .cons parent c, l => parent.toStructUneraseSuffix (.cons c l)
  | .listAppendLeft parent right, left => parent.toStructUneraseSuffix (.listAppend left right.unerase)
  | .listAppendRight parent left, right => parent.toStructUneraseSuffix (.listAppend left right)
  | .ofList parent, l => parent.toStructUneraseSuffix (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.toStructUneraseSuffix (.singleton c)
  | .pushChar parent s, c => parent.toStructUneraseSuffix (.push s c)
  | .consChar parent l, c => parent.toStructUneraseSuffix (.cons c l.unerase)
  | .litChar parent s _ _, _ =>
    parent.toStructUneraseSuffix
      (.stringLit { s with
        endExclusive := s.str.endPos, startInclusive_le_endExclusive := by simp })

def Traverser.visitLeft : Traverser → Option Traverser
  | ⟨p, .stringAppend l r⟩ =>
    if l.isEmpty then
      some ⟨.stringAppendRight p l, r⟩
    else
      some ⟨.stringAppendLeft p r, l⟩
  | ⟨p, .push s c⟩ =>
    if s.isEmpty then
      some ⟨.pushChar p s, c⟩
    else
      some ⟨.push p c, s⟩
  | ⟨p, .ofList l⟩ => some ⟨.ofList p, l⟩
  | ⟨p, .singleton c⟩ => some ⟨.singletonChar p, c⟩
  | ⟨p, .stringLit s⟩ =>
    if h : s.str.isEmpty then
      none
    else
      have h : s.str.startPos ≠ s.str.endPos := by simpa using h
      some ⟨.litChar p s s.str.startPos h, .litChar _ _ h⟩
  | ⟨p, .cons c l⟩ => some ⟨.consChar p l, c⟩
  | ⟨p, .listAppend l r⟩ =>
    if l.isEmpty then
      some ⟨.listAppendRight p l, r⟩
    else
      some ⟨.listAppendLeft p r, l⟩
  | ⟨p, .toList s⟩ => some ⟨.toList p, s⟩
  | ⟨p, .anyString _⟩ => none
  | ⟨p, .erasedString _⟩ => none
  | ⟨p, .nil⟩ => none
  | ⟨p, .anyList l⟩ => none
  | ⟨p, .erasedList _⟩ => none
  | ⟨p, .charLit c⟩ => none
  | ⟨p, .anyChar c⟩ => none
  | ⟨p, .erasedChar c⟩ => none

def Traverser.visitRight : Traverser → Option Traverser
  | ⟨p, .stringAppend l r⟩ =>
    if r.isEmpty then
      some ⟨.stringAppendLeft p r, l⟩
    else
      some ⟨.stringAppendRight p l, r⟩
  | ⟨p, .push s c⟩ => some ⟨.pushChar p s, c⟩
  | ⟨p, .ofList l⟩ => some ⟨.ofList p, l⟩
  | ⟨p, .singleton c⟩ => some ⟨.singletonChar p, c⟩
  | ⟨p, .stringLit s⟩ =>
    if h : s.str.isEmpty then
      none
    else
      have h : s.str.endPos ≠ s.str.startPos := by rw [ne_comm]; simpa using h
      have h' : s.str.endPos.prev h ≠ s.str.endPos := by simp
      some ⟨.litChar p s _ h', .litChar _ _ h'⟩
  | ⟨p, .cons c l⟩ =>
    if l.isEmpty then
      some ⟨.consChar p l, c⟩
    else
      some ⟨.cons p c, l⟩
  | ⟨p, .listAppend l r⟩ =>
    if r.isEmpty then
      some ⟨.listAppendLeft p r, l⟩
    else
      some ⟨.listAppendRight p l, r⟩
  | ⟨p, .toList s⟩ => some ⟨.toList p, s⟩
  | ⟨p, .anyString _⟩ => none
  | ⟨p, .erasedString _⟩ => none
  | ⟨p, .nil⟩ => none
  | ⟨p, .anyList l⟩ => none
  | ⟨p, .erasedList _⟩ => none
  | ⟨p, .charLit c⟩ => none
  | ⟨p, .anyChar c⟩ => none
  | ⟨p, .erasedChar c⟩ => none

def Path.nextLeft : Path ty → ExprStructure ty → Traverser ⊕ ExprStructure .string
  | .root, e => .inr e
  -- String
  | .stringAppendLeft parent right, left =>
    if right.isEmpty then
      parent.nextLeft (.stringAppend left right)
    else
      .inl ⟨.stringAppendRight parent left, right⟩
  | .stringAppendRight parent left, right =>
    parent.nextLeft (.stringAppend left right)
  | .push parent c, s => .inl ⟨.pushChar parent s, c⟩
  | .toList parent, s => parent.nextLeft (.toList s)
  -- List Char
  | .cons parent c, l => parent.nextLeft (.cons c l)
  | .listAppendLeft parent right, left =>
    if right.isEmpty then
      parent.nextLeft (.listAppend left right)
    else
      .inl ⟨.listAppendRight parent left, right⟩
  | .listAppendRight parent left, right =>
    parent.nextLeft (.listAppend left right)
  | .ofList parent, l => parent.nextLeft (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.nextLeft (.singleton c)
  | .pushChar parent s, c => parent.nextLeft (.push s c)
  | .consChar parent l, c =>
    if l.isEmpty then
      parent.nextLeft (.cons c l)
    else
      .inl ⟨.cons parent c, l⟩
  | .litChar parent s p h, _ =>
    let s := { s with
      startInclusive := if p.next h ≤ s.endExclusive then p.next h else s.startInclusive,
      startInclusive_le_endExclusive := by split <;> simp [*, s.startInclusive_le_endExclusive] }
    if h'' : p.next h = s.str.endPos then
      parent.nextLeft (.stringLit s)
    else
      .inl ⟨.litChar parent s (p.next h) h'', .litChar s (p.next h) h''⟩

def Path.nextRight : Path ty → ExprStructure ty → Traverser ⊕ ExprStructure .string
  | .root, e => .inr e
  -- String
  | .stringAppendLeft parent right, left =>
    parent.nextRight (.stringAppend left right)
  | .stringAppendRight parent left, right =>
    if left.isEmpty then
      parent.nextRight (.stringAppend left right)
    else
      .inl ⟨.stringAppendLeft parent right, left⟩
  | .push parent c, s => parent.nextRight (.push s c)
  | .toList parent, s => parent.nextRight (.toList s)
  -- List Char
  | .cons parent c, l => .inl ⟨.consChar parent l, c⟩
  | .listAppendLeft parent right, left =>
    parent.nextRight (.listAppend left right)
  | .listAppendRight parent left, right =>
    if left.isEmpty then
      parent.nextRight (.listAppend left right)
    else
      .inl ⟨.listAppendLeft parent right, left⟩
  | .ofList parent, l => parent.nextRight (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.nextRight (.singleton c)
  | .pushChar parent s, c =>
    if s.isEmpty then
      parent.nextRight (.push s c)
    else
      .inl ⟨.push parent c, s⟩
  | .consChar parent l, c => parent.nextRight (.cons c l)
  | .litChar parent s p _, _ =>
    let s := { s with
      endExclusive := if s.startInclusive ≤ p then p else s.endExclusive,
      startInclusive_le_endExclusive := by split <;> simp [*, s.startInclusive_le_endExclusive] }
    if h : p = s.str.startPos then
      parent.nextRight (.stringLit s)
    else
      .inl ⟨.litChar parent s (p.prev h) (by simp +zetaDelta),
        .litChar s (p.prev h) (by simp +zetaDelta)⟩

def obviousCharDiseq (a : ExprStructure ty) (b : ExprStructure ty') : Bool :=
  match a, b with
  | .charLit c, .charLit c' => c != c'
  | _, _ => false

def cancelLeft (a b : ExprStructure .string) :
    MetaM (Array CancelElement × ExprStructure .string × ExprStructure .string) := do
  if a.isEmpty || b.isEmpty then
    return (#[], a, b)
  let mut ta : Traverser := .root a
  let mut tb : Traverser := .root b
  let mut els : Array CancelElement := #[]
  -- invariants:
  -- `isDefEq (ta.path.toStruct ta.expr).toExpr a` and
  -- `isDefEq (tb.path.toStruct tb.expr).toExpr b` and
  -- `(els.map (·.left)).toList = ta.path.prefix` and
  -- `(els.map (·.right)).toList = tb.path.prefix` and
  -- `ta.expr.elements ≠ []` and `tb.expr.elements ≠ []`
  repeat
    if ← pure (ta.expr.maxDepth == tb.expr.maxDepth) then
      if let some ⟨hty⟩ ← ta.expr.isCompatibleWith tb.expr then
      let (aexpr, bexpr) : ExprStructure ta.type × ExprStructure tb.type ← match h : ta.type with
        | .char =>
          if ← ta.expr.isDefEq (hty ▸ tb.expr) then
            els := els.push (.char ta.expr.toExpr)
            pure (h ▸ .erasedChar ta.expr.toExpr, hty ▸ h ▸ .erasedChar ta.expr.toExpr)
          else
            els := els.push (.cons ta.expr.toExpr tb.expr.toExpr)
            pure (h ▸ .erasedChar ta.expr.toExpr, hty ▸ h ▸ .erasedChar tb.expr.toExpr)
        | .list =>
          els := els.push (.list ta.expr.toExpr)
          pure (h ▸ .erasedList ta.expr.toExpr, hty ▸ h ▸ .erasedList ta.expr.toExpr)
        | .string =>
          els := els.push (.string ta.expr.toExpr)
          pure (h ▸ .erasedString ta.expr.toExpr, hty ▸ h ▸ .erasedString ta.expr.toExpr)
      let ta' := ta.path.nextLeft aexpr
      let tb' := tb.path.nextLeft bexpr
      match ta', tb' with
      | .inl ta', .inl tb' =>
        if obviousCharDiseq ta.expr tb.expr then
          -- for the char diseq procedure we need that only one half is erased
          -- if the other half is already erased, then unerase it
          return (els, ta'.path.toStructUneraseSuffix ta'.expr.unerase,
            tb'.path.toStructUneraseSuffix tb'.expr.unerase)
        ta := ta'; tb := tb'
        continue
      | .inl ta', .inr b' => return (els, ta'.path.toStruct ta'.expr, b')
      | .inr a', .inl tb' => return (els, a', tb'.path.toStruct tb'.expr)
      | .inr a', .inr b' => return (els, a', b')
    if ta.expr.maxDepth ≤ tb.expr.maxDepth then
      if let some tb' := tb.visitLeft then
        tb := tb'
        continue
    if tb.expr.maxDepth ≤ ta.expr.maxDepth then
      if let some ta' := ta.visitLeft then
        ta := ta'
        continue
    return (els, ta.path.toStruct ta.expr, tb.path.toStruct tb.expr)
  unreachable!

def cancelRight (a b : ExprStructure .string) :
    MetaM (Array CancelElement × ExprStructure .string × ExprStructure .string) := do
  if a.isEmpty || b.isEmpty then
    return (#[], a, b)
  let mut ta : Traverser := .root a
  let mut tb : Traverser := .root b
  let mut els : Array CancelElement := #[]
  -- invariants:
  -- `isDefEq (ta.path.toStruct ta.expr).toExpr a` and
  -- `isDefEq (tb.path.toStruct tb.expr).toExpr b` and
  -- `(els.map (·.left)).toList = ta.path.prefix` and
  -- `(els.map (·.right)).toList = tb.path.prefix` and
  -- `ta.expr.elements ≠ []` and `tb.expr.elements ≠ []`
  repeat
    if ← pure (ta.expr.maxDepth == tb.expr.maxDepth) then
      if let some ⟨hty⟩ ← ta.expr.isCompatibleWith tb.expr then
      let (aexpr, bexpr) : ExprStructure ta.type × ExprStructure tb.type ← match h : ta.type with
        | .char =>
          if ← ta.expr.isDefEq (hty ▸ tb.expr) then
            els := els.push (.char ta.expr.toExpr)
            pure (h ▸ .erasedChar ta.expr.toExpr, hty ▸ h ▸ .erasedChar ta.expr.toExpr)
          else
            els := els.push (.cons ta.expr.toExpr tb.expr.toExpr)
            pure (h ▸ .erasedChar ta.expr.toExpr, hty ▸ h ▸ .erasedChar tb.expr.toExpr)
        | .list =>
          els := els.push (.list ta.expr.toExpr)
          pure (h ▸ .erasedList ta.expr.toExpr, hty ▸ h ▸ .erasedList ta.expr.toExpr)
        | .string =>
          els := els.push (.string ta.expr.toExpr)
          pure (h ▸ .erasedString ta.expr.toExpr, hty ▸ h ▸ .erasedString ta.expr.toExpr)
      let ta' := ta.path.nextRight aexpr
      let tb' := tb.path.nextRight bexpr
      match ta', tb' with
      | .inl ta', .inl tb' =>
        if obviousCharDiseq ta.expr tb.expr then
          -- for the char diseq procedure we need that only one half is erased
          -- if the other half is already erased, then unerase it
          return (els, ta'.path.toStructUnerasePrefix ta'.expr.unerase,
            tb'.path.toStructUnerasePrefix tb'.expr.unerase)
        ta := ta'; tb := tb'
        continue
      | .inl ta', .inr b' => return (els, ta'.path.toStruct ta'.expr, b')
      | .inr a', .inl tb' => return (els, a', tb'.path.toStruct tb'.expr)
      | .inr a', .inr b' => return (els, a', b')
    if ta.expr.maxDepth ≤ tb.expr.maxDepth then
      if let some tb' := tb.visitRight then
        tb := tb'
        continue
    if tb.expr.maxDepth ≤ ta.expr.maxDepth then
      if let some ta' := ta.visitRight then
        ta := ta'
        continue
    return (els, ta.path.toStruct ta.expr, tb.path.toStruct tb.expr)
  unreachable!

def mkEvalNilRefl (structExpr : Expr) : Expr :=
  mkApp2 (.const ``Eq.refl [1]) (.app (.const ``List [0]) (mkConst ``Char))
    (mkApp2 (mkConst ``StringStructure.eval) structExpr
      (.app (.const ``List.nil [0]) (mkConst ``Char)))

def collectCancelEqs (a : Array CancelElement) : Array Expr :=
  a.filterMap fun
    | .cons a b => some <| mkApp3 (.const ``Eq [1]) (mkConst ``Char) a b
    | _ => none

public section

builtin_simproc simpEq ((_ : String) = _) := fun e => withNewMCtxDepth do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let lhs := e.appFn!.appArg!
  let rhs := e.appArg!
  if lhs.isStringLit && rhs.isStringLit then
    return .continue -- handled in reduceEq, not here
  unless (← getEnv).contains ``StringStructure do
    return .continue -- insufficient imports
  let lhsStruct ← createStringStructure lhs
  let rhsStruct ← createStringStructure rhs
  if lhsStruct matches .anyString _ && rhsStruct matches .anyString _ then
    -- nothing to match on
    return .continue
  let (els, lhsStruct, rhsStruct) ← cancelLeft lhsStruct rhsStruct
  if let some (.cons c₁@(mkCharLit a) c₂@(mkCharLit b)) := els.back? then
    if Char.ofNat a != Char.ofNat b then
      -- char diseq left
      let (lhsStructErased, lhsStruct) := lhsStruct.removeErasedTop
      let (rhsStructErased, rhsStruct) := rhsStruct.removeErasedTop
      let proof := mkApp10 (mkConst ``StringStructure.denote_ne_left)
        lhsStruct.toStructExpr rhsStruct.toStructExpr
        lhsStructErased.toStructExpr rhsStructErased.toStructExpr
        (cancelElementsToStructExpr els.pop) c₁ c₂ reflBoolFalse
        (mkEvalNilRefl lhsStruct.toStructExpr) (mkEvalNilRefl rhsStruct.toStructExpr)
      return .done { expr := mkConst ``False, proof? := proof }
  if lhsStruct.allErased && rhsStruct.allErased then
    let eqs := collectCancelEqs els
    if eqs.isEmpty then
      -- equality modulo associativity
      let proof := mkApp3 (mkConst ``StringStructure.denote_eq)
        lhsStruct.toStructExpr rhsStruct.toStructExpr (mkEvalNilRefl lhsStruct.toStructExpr)
      return .done { expr := mkConst ``True, proof? := proof }
    -- reduction to character equalities
    let proof := mkApp5 (mkConst ``StringStructure.denote_char_inj)
      lhsStruct.toStructExpr rhsStruct.toStructExpr (cancelElementsToStructExpr els)
      (mkEvalNilRefl lhsStruct.toStructExpr) (mkEvalNilRefl rhsStruct.toStructExpr)
    return .visit { expr := mkAndN eqs.toList, proof? := proof }
  let (els', lhsStruct, rhsStruct) ← cancelRight lhsStruct rhsStruct
  if let some (.cons c₁@(mkCharLit a) c₂@(mkCharLit b)) := els'.back? then
    if Char.ofNat a != Char.ofNat b then
      -- char diseq right
      let (lhsStructErased, lhsStruct) := lhsStruct.removeErasedTop
      let (rhsStructErased, rhsStruct) := rhsStruct.removeErasedTop
      let proof := mkApp10 (mkConst ``StringStructure.denote_ne_right)
        lhsStruct.toStructExpr rhsStruct.toStructExpr
        lhsStructErased.toStructExpr rhsStructErased.toStructExpr
        (cancelElementsToStructExpr els'.pop.reverse) c₁ c₂ reflBoolFalse
        (mkEvalNilRefl lhsStruct.toStructExpr) (mkEvalNilRefl rhsStruct.toStructExpr)
      return .done { expr := mkConst ``False, proof? := proof }
  if els.isEmpty && els'.isEmpty then
    return .continue
  let (lhsStructErased, lhsStruct) := lhsStruct.removeErasedTop
  let (rhsStructErased, rhsStruct) := rhsStruct.removeErasedTop
  -- general case: equality of characters + center string equality
  let proof := mkApp8 (mkConst ``StringStructure.denote_cancel)
    lhsStruct.toStructExpr rhsStruct.toStructExpr
    lhsStructErased.toStructExpr rhsStructErased.toStructExpr
    (cancelElementsToStructExpr els) (cancelElementsToStructExpr els'.reverse)
    (mkEvalNilRefl lhsStruct.toStructExpr) (mkEvalNilRefl rhsStruct.toStructExpr)
  let eqs := collectCancelEqs els
  let eqs' := collectCancelEqs els'.reverse
  let lhsMid := lhsStructErased.toExpr
  let rhsMid := rhsStructErased.toExpr
  let midEq := mkApp3 (.const ``Eq [1]) (mkConst ``String) lhsMid rhsMid
  return .visit { expr := mkAndN (eqs.toList ++ midEq :: eqs'.toList), proof? := proof }
