/-
Copyright (c) 2026 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
import Init.Data.String.SimpEq
import Init.Data.String.Lemmas.FindPos
import Init.While
public meta import Lean.Elab.Command

meta section

namespace String

open Lean Meta
open Internal.SimpEq

inductive ExprType where
  | string
  | list
  | char
deriving DecidableEq, Repr

deriving instance Repr for String.Pos
deriving instance Repr for Slice

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
deriving Repr

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

def listAppendInst : Expr :=
  mkApp2 (.const ``instHAppendOfAppend [0]) (.app (mkConst ``List) (mkConst ``Char))
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
      (.app (mkConst ``List) (mkConst ``Char)) (.app (mkConst ``List) (mkConst ``Char))
      (.app (mkConst ``List) (mkConst ``Char)) listAppendInst
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
  | result (x : ExprStructure ty)

@[inline]
def ErasureResult.valueD (x : ErasureResult ty) (default : ExprStructure ty) :
    ExprStructure ty :=
  match x with
  | .result x => x
  | _ => default

@[inline]
def ErasureResult.elim (x : ErasureResult ty) (empty noErased : ExprStructure ty) :
    ExprStructure ty :=
  match x with
  | .empty => empty
  | .noErased => noErased
  | .result x => x

@[inline]
def ErasureResult.withErased (x : ErasureResult ty) (val : ExprStructure ty) :
    ErasureResult ty :=
  match x with
  | .noErased => .result val.toAny
  | x => x

@[inline]
def ErasureResult.map (f : ExprStructure ty → ExprStructure ty') :
    ErasureResult ty → ErasureResult ty'
  | .empty => .empty
  | .noErased => .noErased
  | .result x => .result (f x)

def ExprStructure.removeErased : ExprStructure ty → ErasureResult ty
  -- String
  | .stringAppend a b =>
    match a.removeErased, b.removeErased with
    | .empty, res => res.withErased b
    | res, .empty => res.withErased a
    | .noErased, .noErased => .noErased
    | res, res' => .result (.stringAppend (res.valueD a) (res'.valueD b))
  | .push s c =>
    match s.removeErased, c.removeErased with
    | .empty, .empty => .empty
    | .empty, res => (res.withErased c).map .singleton
    | res, .empty => res.withErased s
    | .noErased, .noErased => .noErased
    | res, res' => .result (.push (res.valueD s) (res'.valueD c))
  | .singleton c => c.removeErased.map .singleton
  | .ofList l => l.removeErased.map .ofList
  | .stringLit s =>
    if s.startInclusive = s.str.startPos ∧ s.endExclusive = s.str.endPos then
      .noErased
    else if s.isEmpty then
      .empty
    else
      .result (.stringLit s.copy)
  | .anyString _ => .noErased
  | .erasedString _ => .empty
  -- List Char
  | .nil => .noErased
  | .cons c l =>
    match c.removeErased, l.removeErased with
    | .empty, res => if l matches .nil then .empty else res.withErased l
    | .noErased, .empty | .result c, .empty => .result (.cons c .nil)
    | .noErased, .noErased => .noErased
    | res, res' => .result (.cons (res.valueD c) (res'.valueD l))
  | .listAppend a b =>
    match a.removeErased, b.removeErased with
    | .empty, res => res.withErased b
    | res, .empty => res.withErased a
    | .noErased, .noErased => .noErased
    | res, res' => .result (.listAppend (res.valueD a) (res'.valueD b))
  | .toList l => l.removeErased.map .toList
  | .anyList _ => .noErased
  | .erasedList _ => .empty
  -- Char
  | .charLit _ => .noErased
  | .anyChar _ => .noErased
  | .erasedChar _ => .empty

def ExprStructure.removeErasedTop (e : ExprStructure .string) : ExprStructure .string :=
  match e.removeErased with
  | .empty => .stringLit ""
  | .noErased => e.toAny
  | .result x => x

inductive CancelElement where
  | cons (l r : Expr)
  | string (e : Expr)
  | list (e : Expr)
  | char (e : Expr)
deriving Repr

def cancelElementToStruct (as : Array CancelElement) : Expr :=
  as.foldr (init := mkConst ``Cancellation.nil) fun
    | .cons l r, s => mkApp3 (mkConst ``Cancellation.cons) l r s
    | .string e, s => mkApp2 (mkConst ``Cancellation.string) e s
    | .list e, s => mkApp2 (mkConst ``Cancellation.list) e s
    | .char e, s => mkApp2 (mkConst ``Cancellation.char) e s

inductive Element where
  | string (e : Expr)
  | list (e : Expr)
  | char (e : Expr)

def CancelElement.left : CancelElement → Element
  | .cons l _ => .char l
  | .string e => .string e
  | .list e => .list e
  | .char e => .char e

def CancelElement.right : CancelElement → Element
  | .cons _ r => .char r
  | .string e => .string e
  | .list e => .list e
  | .char e => .char e

def ExprStructure.elements : ExprStructure ty → List Element
  -- String
  | .stringAppend a b => a.elements ++ b.elements
  | .push s c => s.elements ++ c.elements
  | .singleton c => c.elements
  | .ofList l => l.elements
  | .stringLit s => s.str.toList.map (fun c => .char (mkCharLit c.toNat))
  | .anyString s | .erasedString s => [.string s]
  -- List Char
  | .nil => []
  | .cons c l => c.elements ++ l.elements
  | .listAppend a b => a.elements ++ b.elements
  | .toList s => s.elements
  | .anyList l | .erasedList l => [.list l]
  -- Char
  | .charLit c => [.char (mkCharLit c.toNat)]
  | .anyChar c | .erasedChar c => [.char c]

@[local simp]
theorem ExprStructure.elements_char_ne_nil (e : ExprStructure .char) :
    e.elements ≠ [] := by
  cases e <;> simp [elements]

@[local simp]
theorem ExprStructure.isEmpty_iff_elements_eq_nil (e : ExprStructure ty) :
    e.isEmpty ↔ e.elements = [] := by
  fun_induction isEmpty <;> simp_all [elements]

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
deriving Repr

def ExprStructure.litChar (s : String.Slice) (p : s.str.Pos) (h : p ≠ s.str.endPos) :
    ExprStructure .char :=
  if s.startInclusive ≤ p ∧ p < s.endExclusive then
    .charLit (p.get h)
  else
    .erasedChar (mkCharLit (p.get h).toNat)

@[local simp]
theorem ExprStructure.elements_litChar (s : String.Slice) (p : s.str.Pos) (h : p ≠ s.str.endPos) :
    (litChar s p h).elements = [.char (mkCharLit (p.get h).toNat)] := by
  fun_cases litChar <;> simp [elements]

@[unbox]
structure Traverser where
  {type : ExprType}
  path : Path type
  expr : ExprStructure type
  of_eq_litChar (pa s p h) (h' : type = .char) :
    h' ▸ path = .litChar pa s p h → expr = h' ▸ .litChar s p h
deriving Repr

def Traverser.root (e : ExprStructure .string) : Traverser := ⟨.root, e, nofun⟩

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

def Path.prefix : Path ty → List Element
  | .root => []
  -- String
  | .stringAppendLeft parent _ => parent.prefix
  | .stringAppendRight parent left => parent.prefix ++ left.elements
  | .push parent _ => parent.prefix
  | .toList parent => parent.prefix
  -- List Char
  | .cons parent c => parent.prefix ++ c.elements
  | .listAppendLeft parent _ => parent.prefix
  | .listAppendRight parent left => parent.prefix ++ left.elements
  | .ofList parent => parent.prefix
  -- Char
  | .singletonChar parent => parent.prefix
  | .pushChar parent s => parent.prefix ++ s.elements
  | .consChar parent _ => parent.prefix
  | .litChar parent s p _ =>
    parent.prefix ++ (s.str.sliceTo p).copy.toList.map (.char <| mkCharLit ·.toNat)

def Path.suffix : Path ty → List Element
  | .root => []
  -- String
  | .stringAppendLeft parent right => right.elements ++ parent.suffix
  | .stringAppendRight parent _ => parent.suffix
  | .push parent c => c.elements ++ parent.suffix
  | .toList parent => parent.suffix
  -- List Char
  | .cons parent _ => parent.suffix
  | .listAppendLeft parent right => right.elements ++ parent.suffix
  | .listAppendRight parent _ => parent.suffix
  | .ofList parent => parent.suffix
  -- Char
  | .singletonChar parent => parent.suffix
  | .pushChar parent _ => parent.suffix
  | .consChar parent l => l.elements ++ parent.suffix
  | .litChar parent s p h =>
    (s.str.sliceFrom (p.next h)).copy.toList.map (.char <| mkCharLit ·.toNat) ++ parent.suffix

theorem Path.elements_toStruct (t : Traverser) :
    (t.path.toStruct t.expr).elements = t.path.prefix ++ (t.expr.elements ++ t.path.suffix) := by
  rcases t with ⟨path, expr, h⟩; dsimp only
  fun_induction toStruct with (try simp [Path.prefix, Path.suffix, ExprStructure.elements, *]; done)
  | case13 parent s p hp expr ih =>
    specialize h parent s p hp rfl rfl
    simp only [ne_eq, reduceCtorEq, forall_false, implies_true, ih, h]
    simp [ExprStructure.elements, Path.prefix, Path.suffix]
    conv => lhs; rw [String.Pos.eq_copy_sliceTo_append_get hp]
    simp

def Traverser.visitLeft : Traverser → Option Traverser
  | ⟨p, .stringAppend l r, _⟩ =>
    if l.isEmpty then
      some ⟨.stringAppendRight p l, r, nofun⟩
    else
      some ⟨.stringAppendLeft p r, l, nofun⟩
  | ⟨p, .push s c, _⟩ =>
    if s.isEmpty then
      some ⟨.pushChar p s, c, nofun⟩
    else
      some ⟨.push p c, s, nofun⟩
  | ⟨p, .ofList l, _⟩ => some ⟨.ofList p, l, nofun⟩
  | ⟨p, .singleton c, _⟩ => some ⟨.singletonChar p, c, nofun⟩
  | ⟨p, .stringLit s, _⟩ =>
    if h : s.str.isEmpty then
      none
    else
      have h : s.str.startPos ≠ s.str.endPos := by simpa using h
      some ⟨.litChar p s s.str.startPos h, .litChar _ _ h, by rintro _ _ _ _ _ ⟨⟩; rfl⟩
  | ⟨p, .cons c l, _⟩ => some ⟨.consChar p l, c, nofun⟩
  | ⟨p, .listAppend l r, _⟩ =>
    if l.isEmpty then
      some ⟨.listAppendRight p l, r, nofun⟩
    else
      some ⟨.listAppendLeft p r, l, nofun⟩
  | ⟨p, .toList s, _⟩ => some ⟨.toList p, s, nofun⟩
  | ⟨p, .anyString _, _⟩ => none
  | ⟨p, .erasedString _, _⟩ => none
  | ⟨p, .nil, _⟩ => none
  | ⟨p, .anyList l, _⟩ => none
  | ⟨p, .erasedList _, _⟩ => none
  | ⟨p, .charLit c, _⟩ => none
  | ⟨p, .anyChar c, _⟩ => none
  | ⟨p, .erasedChar c, _⟩ => none

theorem Traverser.toStruct_of_visitLeft_eq_some {t t' : Traverser}
    (h : t.visitLeft = some t') : t.path.toStruct t.expr = t'.path.toStruct t'.expr := by
  revert h; fun_cases visitLeft <;> rintro ⟨⟩ <;> simp [Path.toStruct]

theorem Traverser.prefix_visitLeft_eq {t t' : Traverser}
    (h : t.visitLeft = some t') : t'.path.prefix = t.path.prefix := by
  revert h; fun_cases visitLeft <;> rintro ⟨⟩ <;> simp_all [Path.prefix]

def Traverser.visitRight : Traverser → Option Traverser
  | ⟨p, .stringAppend l r, _⟩ =>
    if r.isEmpty then
      some ⟨.stringAppendLeft p r, l, nofun⟩
    else
      some ⟨.stringAppendRight p l, r, nofun⟩
  | ⟨p, .push s c, _⟩ => some ⟨.pushChar p s, c, nofun⟩
  | ⟨p, .ofList l, _⟩ => some ⟨.ofList p, l, nofun⟩
  | ⟨p, .singleton c, _⟩ => some ⟨.singletonChar p, c, nofun⟩
  | ⟨p, .stringLit s, _⟩ =>
    if h : s.str.isEmpty then
      none
    else
      have h : s.str.endPos ≠ s.str.startPos := by rw [ne_comm]; simpa using h
      have h' : s.str.endPos.prev h ≠ s.str.endPos := by simp
      some ⟨.litChar p s _ h', .litChar _ _ h', by rintro _ _ _ _ _ ⟨⟩; rfl⟩
  | ⟨p, .cons c l, _⟩ =>
    if l.isEmpty then
      some ⟨.consChar p l, c, nofun⟩
    else
      some ⟨.cons p c, l, nofun⟩
  | ⟨p, .listAppend l r, _⟩ =>
    if r.isEmpty then
      some ⟨.listAppendLeft p r, l, nofun⟩
    else
      some ⟨.listAppendRight p l, r, nofun⟩
  | ⟨p, .toList s, _⟩ => some ⟨.toList p, s, nofun⟩
  | ⟨p, .anyString _, _⟩ => none
  | ⟨p, .erasedString _, _⟩ => none
  | ⟨p, .nil, _⟩ => none
  | ⟨p, .anyList l, _⟩ => none
  | ⟨p, .erasedList _, _⟩ => none
  | ⟨p, .charLit c, _⟩ => none
  | ⟨p, .anyChar c, _⟩ => none
  | ⟨p, .erasedChar c, _⟩ => none

theorem Traverser.toStruct_of_visitRight_eq_some {t t' : Traverser}
    (h : t.visitRight = some t') : t.path.toStruct t.expr = t'.path.toStruct t'.expr := by
  revert h; fun_cases visitRight <;> rintro ⟨⟩ <;> simp [Path.toStruct]

theorem Traverser.suffix_visitRight_eq {t t' : Traverser}
    (h : t.visitRight = some t') : t'.path.suffix = t.path.suffix := by
  revert h; fun_cases visitRight <;> rintro ⟨⟩ <;> simp_all [Path.suffix]

def Path.nextLeft : Path ty → ExprStructure ty → Traverser ⊕ ExprStructure .string
  | .root, e => .inr e
  -- String
  | .stringAppendLeft parent right, left =>
    if right.isEmpty then
      parent.nextLeft (.stringAppend left right)
    else
      .inl ⟨.stringAppendRight parent left, right, nofun⟩
  | .stringAppendRight parent left, right =>
    parent.nextLeft (.stringAppend left right)
  | .push parent c, s => .inl ⟨.pushChar parent s, c, nofun⟩
  | .toList parent, s => parent.nextLeft (.toList s)
  -- List Char
  | .cons parent c, l => parent.nextLeft (.cons c l)
  | .listAppendLeft parent right, left =>
    if right.isEmpty then
      parent.nextLeft (.listAppend left right)
    else
      .inl ⟨.listAppendRight parent left, right, nofun⟩
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
      .inl ⟨.cons parent c, l, nofun⟩
  | .litChar parent s p h, _ =>
    let s := { s with
      startInclusive := if p.next h ≤ s.endExclusive then p.next h else s.startInclusive,
      startInclusive_le_endExclusive := by split <;> simp [*, s.startInclusive_le_endExclusive] }
    if h'' : p.next h = s.str.endPos then
      parent.nextLeft (.stringLit s)
    else
      .inl ⟨.litChar parent s (p.next h) h'', .litChar s (p.next h) h'', by rintro _ _ _ _ _ ⟨⟩; rfl⟩

theorem Path.nextLeft_matches_inl_iff {p : Path ty} {e : ExprStructure ty} :
    p.nextLeft e matches .inl _ ↔ p.suffix ≠ [] := by
  fun_induction nextLeft <;> simp_all +zetaDelta [suffix]

theorem Path.prefix_nextLeft {t t' : Traverser} (h' : t.path.nextLeft t.expr = .inl t') :
    t'.path.prefix = t.path.prefix ++ t.expr.elements := by
  rcases t with ⟨path, expr, h⟩; revert h'; dsimp only
  fun_induction nextLeft with
    (try (first | rintro ⟨⟩ | intro) <;> simp_all [Path.prefix, ExprStructure.elements]; done)
  | case16 parent s p hp s' hp' c ih =>
    cases h _ _ _ _ rfl rfl; clear h
    intro h'; rw [ih nofun h']; clear ih h'
    simp only [ExprStructure.elements, Path.prefix, List.append_assoc, List.append_cancel_left_eq]
    conv => lhs; rw [String.Pos.eq_copy_sliceTo_append_get hp, hp']
    simp [s']
  | case17 parent s p hp s' hp' c =>
    cases h _ _ _ _ rfl rfl; clear h
    rintro ⟨⟩; dsimp only
    simp only [Path.prefix, ExprStructure.elements_litChar, List.append_assoc,
      List.append_cancel_left_eq]
    have : (s.str.sliceTo (p.next hp)).copy = (s.str.sliceTo p).copy ++ String.singleton (p.get hp) := by
      rw [sliceTo_copy_eq_iff_exists_splits]
      exact ⟨_, p.splits_next hp⟩
    simp [s', this]

theorem Path.suffix_nextLeft {t t' : Traverser} (h' : t.path.nextLeft t.expr = .inl t') :
    t'.expr.elements ++ t'.path.suffix = t.path.suffix := by
  rcases t with ⟨path, expr, h⟩; revert h'; dsimp only
  fun_induction nextLeft with
    (try (first | rintro ⟨⟩ | intro) <;> simp_all +zetaDelta [Path.suffix]; done)
  | case17 parent s p hp s' hp' c =>
    cases h _ _ _ _ rfl rfl; clear h
    rintro ⟨⟩; dsimp only
    simp only [ExprStructure.elements_litChar, suffix, List.cons_append, List.nil_append]
    have : (s.str.sliceFrom (p.next hp)).copy =
        String.singleton ((p.next hp).get hp') ++ (s.str.sliceFrom ((p.next hp).next hp')).copy := by
      apply Pos.Splits.copy_sliceFrom_eq
      exact (p.next hp).splits_next_right hp'
    simp [s', this]

def Path.nextRight : Path ty → ExprStructure ty → Traverser ⊕ ExprStructure .string
  | .root, e => .inr e
  -- String
  | .stringAppendLeft parent right, left =>
    parent.nextRight (.stringAppend left right)
  | .stringAppendRight parent left, right =>
    if left.isEmpty then
      parent.nextRight (.stringAppend left right)
    else
      .inl ⟨.stringAppendLeft parent right, left, nofun⟩
  | .push parent c, s => parent.nextRight (.push s c)
  | .toList parent, s => parent.nextRight (.toList s)
  -- List Char
  | .cons parent c, l => .inl ⟨.consChar parent l, c, nofun⟩
  | .listAppendLeft parent right, left =>
    parent.nextRight (.listAppend left right)
  | .listAppendRight parent left, right =>
    if left.isEmpty then
      parent.nextRight (.listAppend left right)
    else
      .inl ⟨.listAppendLeft parent right, left, nofun⟩
  | .ofList parent, l => parent.nextRight (.ofList l)
  -- Char
  | .singletonChar parent, c => parent.nextRight (.singleton c)
  | .pushChar parent s, c =>
    if s.isEmpty then
      parent.nextRight (.push s c)
    else
      .inl ⟨.push parent c, s, nofun⟩
  | .consChar parent l, c => parent.nextRight (.cons c l)
  | .litChar parent s p _, _ =>
    let s := { s with
      endExclusive := if s.startInclusive ≤ p then p else s.endExclusive,
      startInclusive_le_endExclusive := by split <;> simp [*, s.startInclusive_le_endExclusive] }
    if h : p = s.str.startPos then
      parent.nextRight (.stringLit s)
    else
      .inl ⟨.litChar parent s (p.prev h) (by simp +zetaDelta),
        .litChar s (p.prev h) (by simp +zetaDelta), by rintro _ _ _ _ _ ⟨⟩; rfl⟩

theorem Path.nextRight_matches_inl_iff {p : Path ty} {e : ExprStructure ty} :
    p.nextRight e matches .inl _ ↔ p.prefix ≠ [] := by
  fun_induction nextRight <;> simp_all +zetaDelta [Path.prefix]

theorem Path.suffix_nextRight {t t' : Traverser} (h' : t.path.nextRight t.expr = .inl t') :
    t'.path.suffix = t.expr.elements ++ t.path.suffix := by
  rcases t with ⟨path, expr, h⟩; revert h'; dsimp only
  fun_induction nextRight with
    (try (first | rintro ⟨⟩ | intro) <;> simp_all [Path.suffix, ExprStructure.elements]; done)
  | case16 parent s p hp s' hp' c ih =>
    cases h _ _ _ _ rfl rfl; clear h
    intro h'; rw [ih nofun h']; clear ih h'
    simp only [ExprStructure.elements, ExprStructure.elements_litChar, suffix, List.cons_append,
      List.nil_append]
    conv => lhs; rw [String.Pos.eq_copy_sliceTo_append_get hp]
    simp [← hp', s']
  | case17 parent s p hp hp' c =>
    cases h _ _ _ _ rfl rfl; clear h
    rintro ⟨⟩; dsimp only
    simp only [suffix, ExprStructure.elements_litChar, List.cons_append, List.nil_append]
    have : (s.str.sliceFrom p).copy = String.singleton (p.get hp) ++ (s.str.sliceFrom (p.next hp)).copy := by
      apply Pos.Splits.copy_sliceFrom_eq
      exact p.splits_next_right hp
    simp +zetaDelta [this]

theorem Path.prefix_nextRight {t t' : Traverser} (h' : t.path.nextRight t.expr = .inl t') :
    t'.path.prefix ++ t'.expr.elements = t.path.prefix := by
  rcases t with ⟨path, expr, h⟩; revert h'; dsimp only
  fun_induction nextRight with
    (try (first | rintro ⟨⟩ | intro) <;> simp_all +zetaDelta [Path.prefix]; done)
  | case17 parent s p hp s' hp' c =>
    cases h _ _ _ _ rfl rfl; clear h
    rintro ⟨⟩; dsimp only
    simp only [Path.prefix, ExprStructure.elements_litChar, List.append_assoc,
      List.append_cancel_left_eq]
    have : (s.str.sliceTo p).copy = (s.str.sliceTo (p.prev hp')).copy ++
        String.singleton ((p.prev hp').get (by simp)) := by
      apply Pos.Splits.copy_sliceTo_eq
      exact p.splits_prev_right hp'
    simp +zetaDelta [this]

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
          return (els, ta.path.toStruct ta.expr, tb.path.toStruct tb.expr)
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
          return (els, ta.path.toStruct ta.expr, tb.path.toStruct tb.expr)
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

def abc : String := ""

local elab "#test_cancel " l:term ", " r:term : command => do
  Elab.Command.runTermElabM fun _ => do
    let l ← Elab.Term.elabTermEnsuringType l (mkConst ``String)
    let r ← Elab.Term.elabTermEnsuringType r (mkConst ``String)
    Elab.Term.synthesizeSyntheticMVarsUsingDefault
    withNewMCtxDepth do
    withReducible do
    let l ← createStringStructure l
    let r ← createStringStructure r
    logInfo l.toStructExpr
    logInfo r.toStructExpr
    let (els, l, r) ← cancelLeft l r
    let (els', l, r) ← cancelRight l r
    let l := l.removeErased.elim (.stringLit "") l
    let r := r.removeErased.elim (.stringLit "") r
    logInfo m!"Left cancel:{indentExpr (cancelElementToStruct els)}\n\
               Right cancel:{indentExpr (cancelElementToStruct els'.reverse)}\n\
               Left-hand side:{indentExpr l.toExpr}\n\
               Right-hand side:{indentExpr r.toExpr}\n"

variable (s : String) in
#test_cancel "hi something something hd", "h".push 'i' ++ s ++ "hd"

variable (s : String) (l : List Char) in
#test_cancel (String.ofList ('a' :: 'b' :: l)).push 'b' ++ String.singleton 'a', "ab" ++ s ++ "ba"

#eval withReducible <|
  cancelLeft (.stringAppend (.stringLit "hi") (.anyString (.const ``abc []))) (.stringLit "hi there")

public section

builtin_simproc simpEq ((_ : String) = _) := fun e => do
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
  return .continue
