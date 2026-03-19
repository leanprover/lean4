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
public meta import Lean.Elab.Command

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

def ExprStructure.elementsWithoutErased : ExprStructure ty → List Element
  -- String
  | .stringAppend a b => a.elementsWithoutErased ++ b.elementsWithoutErased
  | .push s c => s.elementsWithoutErased ++ c.elementsWithoutErased
  | .singleton c => c.elementsWithoutErased
  | .ofList l => l.elementsWithoutErased
  | .stringLit s => s.copy.toList.map (fun c => .char (mkCharLit c.toNat))
  | .anyString s => [.string s]
  | .erasedString _ => []
  -- List Char
  | .nil => []
  | .cons c l => c.elementsWithoutErased ++ l.elementsWithoutErased
  | .listAppend a b => a.elementsWithoutErased ++ b.elementsWithoutErased
  | .toList s => s.elementsWithoutErased
  | .anyList l => [.list l]
  | .erasedList _ => []
  -- Char
  | .charLit c => [.char (mkCharLit c.toNat)]
  | .anyChar c => [.char c]
  | .erasedChar _ => []

def ErasureResult.erasedElements (res : ErasureResult ty) (e : ExprStructure ty) :
    List Element :=
  match res with
  | .empty => []
  | .noErased => e.toAny.elements
  | .result x _ => x.elements

def ErasureResult.unerasedValue (res : ErasureResult ty) (e : ExprStructure ty) :
    ExprStructure ty :=
  match res with
  | .empty => e
  | .noErased => e.toAny
  | .result _ y => y

@[local simp]
theorem ExprStructure.elementsWithoutErased_toAny (e : ExprStructure ty) :
    e.toAny.elementsWithoutErased = e.toAny.elements := by
  fun_cases toAny <;> rfl

@[local simp]
theorem ExprStructure.toExpr_toAny (e : ExprStructure ty) :
    e.toAny.toExpr = e.toExpr := by
  fun_cases toAny <;> rfl

theorem ErasureResult.erasedElements_map
    {f : ExprStructure ty → ExprStructure ty'}
    {e : ExprStructure ty} {res : ErasureResult ty}
    (hf : ∀ e, (f e).elements = e.elements)
    (hf' : ∀ e, (f e).elementsWithoutErased = e.elementsWithoutErased)
    (hres : res.erasedElements e = (res.unerasedValue e).elementsWithoutErased) :
    (map f res).erasedElements (f e) = ((map f res).unerasedValue (f e)).elementsWithoutErased := by
  fun_cases map <;> simp_all [erasedElements, unerasedValue]

theorem ErasureResult.erasedElements_map₂
    {f : ExprStructure ty → ExprStructure ty' → ExprStructure ty''}
    {lonly : ExprStructure ty → ExprStructure ty''}
    {ronly : ExprStructure ty' → ExprStructure ty''}
    {l : ExprStructure ty} {r : ExprStructure ty'}
    {lres : ErasureResult ty} {rres : ErasureResult ty'}
    (hf : ∀ e e', (f e e').elements = e.elements ++ e'.elements)
    (hf' : ∀ e e', (f e e').elementsWithoutErased = e.elementsWithoutErased ++ e'.elementsWithoutErased)
    (hlonly : ∀ e, (lonly e).elements = e.elements)
    (hronly : ∀ e, (ronly e).elements = e.elements)
    (hlres : lres.erasedElements l = (lres.unerasedValue l).elementsWithoutErased)
    (hrres : rres.erasedElements r = (rres.unerasedValue r).elementsWithoutErased) :
    (map₂ f lonly ronly l r lres rres).erasedElements (f l r) =
      ((map₂ f lonly ronly l r lres rres).unerasedValue (f l r)).elementsWithoutErased := by
  fun_cases map₂ <;> simp_all [erasedElements, unerasedValue]

theorem ExprStructure.erasedElements_removeErased (e : ExprStructure ty) :
    e.removeErased.erasedElements e = (e.removeErased.unerasedValue e).elementsWithoutErased := by
  fun_induction removeErased with
  | case1 | case2 | case3 | case4 | case12 | case13 =>
    simp [ErasureResult.erasedElements_map, ErasureResult.erasedElements_map₂, elements,
      elementsWithoutErased, *]
  | case5 | case6 | case7 | case8 | case9 | case10 | case14 | case15 | case16 | case17 | case18 =>
    simp_all [ErasureResult.erasedElements, elements, ErasureResult.unerasedValue,
      elementsWithoutErased]
  | case11 =>
    apply ErasureResult.erasedElements_map₂ <;> try simp [elements, elementsWithoutErased, *]
    split <;> simp_all [ErasureResult.erasedElements, ErasureResult.unerasedValue,
      elementsWithoutErased]

theorem ErasureResult.toExpr_unerasedValue_map
    {f : ExprStructure ty → ExprStructure ty'} {g : Expr}
    {e : ExprStructure ty} {res : ErasureResult ty}
    (hf : ∀ e, (f e).toExpr = g.app e.toExpr)
    (hres : (res.unerasedValue e).toExpr = e.toExpr) :
    ((map f res).unerasedValue (f e)).toExpr = g.app e.toExpr := by
  fun_cases map <;> simp_all [unerasedValue]

theorem ErasureResult.toExpr_unerasedValue_map₂
    {f : ExprStructure ty → ExprStructure ty' → ExprStructure ty''} {g : Expr}
    {lonly : ExprStructure ty → ExprStructure ty''}
    {ronly : ExprStructure ty' → ExprStructure ty''}
    {l : ExprStructure ty} {r : ExprStructure ty'}
    {lres : ErasureResult ty} {rres : ErasureResult ty'}
    (hf : ∀ e e', (f e e').toExpr = mkApp2 g e.toExpr e'.toExpr)
    (hlres : (lres.unerasedValue l).toExpr = l.toExpr)
    (hrres : (rres.unerasedValue r).toExpr = r.toExpr) :
    ((map₂ f lonly ronly l r lres rres).unerasedValue (f l r)).toExpr =
      mkApp2 g l.toExpr r.toExpr := by
  fun_cases map₂ <;> simp_all [unerasedValue]

theorem ExprStructure.toExpr_unerasedValue (e : ExprStructure ty) :
    (e.removeErased.unerasedValue e).toExpr = e.toExpr := by
  fun_induction removeErased with
  | case1 | case2 | case12 =>
    apply ErasureResult.toExpr_unerasedValue_map₂ <;> simp [toExpr, *]
  | case3 | case4 | case13 =>
    apply ErasureResult.toExpr_unerasedValue_map <;> simp [toExpr, *]
  | case5 | case6 | case7 | case8 | case9 | case10 | case14 | case15 | case16 | case17 | case18 =>
    simp [ErasureResult.unerasedValue]
  | case11 =>
    apply ErasureResult.toExpr_unerasedValue_map₂ <;> try simp [toExpr, *]
    split <;> simp_all [ErasureResult.unerasedValue]

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

/-- Depth-first expression tree traverser -/
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
          logInfo s!"{repr tb'}"
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
  logInfo s!"{repr rhsStruct}"
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
  -- general case: equality of characters + center string equalities
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
