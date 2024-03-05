import Lean.Util.TestNormalForms

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

/-
This file runs many tests on simp and other operations on Boolean/Prop
values.

It is intended to systematically evaluate simp strategies on different
operators.

Note. These tests use the simp tactic not necessarily because simp is
the best strategy for these particular examples, but rather simp may
wind up needing to discharge conditions during rewriting, and we need
tests showing that is has generally effective and predictable --
behavior.

General goals for simp are that the normal forms are sensible to a wide
range of users and that it performs well.  We also strive for Mathlib
compatiblity.
-/

inductive BoolType where
  | prop
  | bool
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

inductive EqOp where
  | eqProp
  | eqBool
  | iffProp
  | beqBool
  deriving BEq, Repr

def EqOp.argType (op : EqOp) : BoolType :=
  match op with
  | .eqProp  | .iffProp => .prop
  | .beqBool | .eqBool => .bool

def EqOp.resultType (op : EqOp) : BoolType :=
  match op with
  | .eqProp | .eqBool | .iffProp => .prop
  | .beqBool => .bool

inductive NeOp where
  | neProp
  | neBool
  | bneBool
  deriving BEq, Repr

def NeOp.argType (op : NeOp) : BoolType :=
  match op with
  | .neProp  => .prop
  | .neBool | .bneBool => .bool

def NeOp.resultType (op : NeOp) : BoolType :=
  match op with
  | .neProp | .neBool  => .prop
  | .bneBool => .bool

inductive IteOp where
  | iteProp
  | iteBool
  | diteProp
  | diteBool
  | condBool
  deriving BEq, Repr

def IteOp.condType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp | .iteBool | .diteBool => .prop
  | .condBool => .bool

def IteOp.resultType (op : IteOp) : BoolType :=
  match op with
  | .iteProp | .diteProp => .prop
  | .iteBool | .diteBool | .condBool => .bool

/--
A first order term representing a `Bool` or `Prop` Lean expression
constructed from the operators described in the module header.

This groups operations that perform the same semantic function into the
same constructor while providing an operator type that identifies the
particular form of it.
-/
inductive BoolVal where
  | trueVal (tp : BoolType)
  | falseVal (tp : BoolType)
  | var (d : VarDecl BoolType)
    /--
    `(t : Prop)` when `t` is a `Bool`.

    Equivalent to `t = true`.
    -/
  | boolToProp (t : BoolVal)
    /-- `decide t` is the same as `p : Bool` -/
  | decide (t : BoolVal)
  | not (x   : BoolVal) (tp : BoolType)
  | and (x y : BoolVal) (tp : BoolType)
  | or  (x y : BoolVal) (tp : BoolType)
  | implies (x y : BoolVal)
  | eq (x y : BoolVal) (op : EqOp)
  | ne (x y : BoolVal) (op : NeOp)
  | ite (c t f : BoolVal) (op : IteOp)
  deriving BEq, Inhabited, Repr

namespace BoolVal

def typeOf (v : BoolVal) : BoolType :=
  match v with
  | .trueVal tp => tp
  | .falseVal tp => tp
  | .var d => d.type
  | .decide _ => .bool
  | .boolToProp _ => .prop
  | .not _ tp => tp
  | .and _ _ tp => tp
  | .or  _ _ tp => tp
  | .implies _ _ => .prop
  | .eq _ _ op => op.resultType
  | .ne _ _ op => op.resultType
  | .ite _ _ _ op => op.resultType

def render [Monad M] [MonadQuotation M] (v : BoolVal) : M Term :=
  match v with
  | .var d => do pure d.ident
  | .trueVal .bool  => `(true)
  | .trueVal .prop  => `(True)
  | .falseVal .bool => `(false)
  | .falseVal .prop => `(False)
  | .boolToProp t => do `(term| ($(←t.render) : Prop))
  | .decide t => do `(term| ($(←t.render) : Bool))
  | .not x .bool => do `(term| !$(←x.render))
  | .not x .prop => do `(term| ¬$(←x.render))
  | .and x y .bool => do `(term| $(←x.render) && $(←y.render))
  | .and x y .prop => do `(term| $(←x.render) ∧  $(←y.render))
  | .or  x y .bool => do `(term| $(←x.render) || $(←y.render))
  | .or  x y .prop => do `(term| $(←x.render) ∨  $(←y.render))
  | .implies x y => do `(term| $(←x.render) → $(←y.render))
  | .eq x y .eqProp | .eq x y .eqBool => do `(term| $(←x.render) = $(←y.render))
  | .eq x y .iffProp => do `(term| $(←x.render) ↔ $(←y.render))
  | .eq x y .beqBool => do `(term| $(←x.render) == $(←y.render))
  | .ne x y .neProp | .ne x y .neBool => do `(term| $(←x.render) ≠ $(←y.render))
  | .ne x y .bneBool => do `(term| $(←x.render) != $(←y.render))
  | .ite c t f op =>
    match op with
    | .iteProp | .iteBool => do
    `(term| if $(←c.render) then $(←t.render) else $(←f.render))
    | .diteProp | .diteBool => do
    `(term| if h : $(←c.render) then $(←t.render) else $(←f.render))
    | .condBool => do
      `(term| bif $(←c.render) then $(←t.render) else $(←f.render))

def map (f : BoolVal -> BoolVal) (v : BoolVal) : BoolVal :=
  match v with
  | .trueVal _ | .falseVal _ | .var _ => v
  | .boolToProp t => .boolToProp (f t)
  | .decide t => .decide (f t)
  | .not x tp   => .not (f x) tp
  | .and x y tp   => .and (f x) (f y) tp
  | .or  x y tp   => .or  (f x) (f y) tp
  | .implies x y => .implies (f x) (f y)
  | .eq x y op => .eq (f x) (f y) op
  | .ne x y op => .ne (f x) (f y) op
  | .ite c x y op => .ite (f c) (f x) (f y) op

def trueProp  : BoolVal := .trueVal .prop
def falseProp : BoolVal := .falseVal .prop
def trueBool  : BoolVal := .trueVal .bool
def falseBool : BoolVal := .falseVal .bool

local prefix:75 "~ " => fun t => BoolVal.not t (BoolVal.typeOf t)
local infix:40 "=v " => fun (x y : BoolVal) =>
  BoolVal.eq x y (match BoolVal.typeOf x with
            | .prop => EqOp.eqProp
            | .bool => EqOp.eqBool)
instance : AndOp BoolVal where
  and x y := BoolVal.and x y (BoolVal.typeOf x)
instance : OrOp BoolVal where
  or x y  := BoolVal.or x y (BoolVal.typeOf x)

section

@[match_pattern]
def iff (x y : BoolVal) : BoolVal := .eq x y .iffProp

@[match_pattern]
def eq_true (x : BoolVal) : BoolVal := .eq x (.trueVal .bool) .eqBool

@[match_pattern]
def eq_false (x : BoolVal) : BoolVal := .eq x (.falseVal .bool) .eqBool

def toBool (v : BoolVal) : BoolVal :=
  match v.typeOf with
  | .prop => .decide v
  | .bool => v

def toProp (v : BoolVal) : BoolVal :=
  match v.typeOf with
  | .prop => v
  | .bool => eq_true v

def coerceType (v : BoolVal) (type : BoolType) : BoolVal :=
  match v.typeOf, type with
  | .prop, .bool => .decide v
  | .bool, .prop => eq_true v
  | _, _ => v

/--
Returns true if we should consider `x` a complement of `y`.

Symmetric so also holds if `y` is a complement of `x`.
-/
def isComplement (x y : BoolVal) : Bool :=
  match x, y with
  | .not x _, y => x == y
  | x, .not y _ => x == y
  | .eq a b _, .ne c d _ => a.typeOf == c.typeOf && a == b && c == d
  | .ne a b _, .eq c d _ => a.typeOf == c.typeOf && a == b && c == d
  | eq_true x, eq_false y => x == y
  | eq_false x, eq_true y => x == y
  | _, _ => false

def resolveEq (thunks : List (term → term → Option term)) (x y : term) : Option term :=
  match thunks with
  | [] => none
  | fn :: thunks =>
    match fn x y with
    | none => resolveEq thunks x y
    | some r => some r

/--
Returns true if we should consider `x` a complement of `y`.

Symmetric so also holds if `y` is a complement of `x`.
-/
def isOrComplement (x y : BoolVal) (tp : BoolType) : Bool :=
  match x, y, tp with
  | .not x _, y, .bool => x == y
  | x, .not y _, .bool => x == y
  | .eq a b _, .ne c d _, _ => a.typeOf == c.typeOf && a == b && c == d
  | .ne a b _, .eq c d _, _ => a.typeOf == c.typeOf && a == b && c == d
  | eq_true x, eq_false y, _ => x == y
  | eq_false x, eq_true y, _ => x == y
  | _, _, _ => false

namespace BoolVal

open BoolType

variable (tp : BoolType)

end BoolVal

partial def simp (v : BoolVal) : BoolVal :=
  let v := map simp v
  match v with
  | .boolToProp b => simp <| eq_true b
  | .decide p =>
      match p with
      | .trueVal  _ => .trueVal  .bool
      | .falseVal _ => .falseVal .bool
      | .not x _   => simp <| ~(.decide x)
      | .and x y _ => simp <| (.decide x) &&& (.decide y)
      | .or x y _  => simp <| (.decide x) ||| (.decide y)
      | .implies p q => simp <| ~(.decide p) ||| (.decide q)
      | .eq x y .eqBool =>
        match y with
        | .trueVal _ => x
        | .falseVal _ => simp (~ x)
        | _ => v
      | .eq x y .eqProp | iff x y =>
        simp <| .eq (.decide x) (.decide y) .beqBool
      | .ne _ _ op =>
        match op with
        | .neProp | .neBool => panic! "Expected ne to be reduced to not eq"
        | .bneBool => panic! "Unexpected bool"
      | .ite c t f op =>
        match op with
        | .iteProp => simp <| .ite c (.decide t) (.decide f) .iteBool
        | _ => v
      | .var _ => v
      | .boolToProp _ => panic! "Expected boolToProp to simplify away"
      | .decide _ | .eq _ _ _ =>
        panic! s!"Unexpected prop {repr p} when bool expected."
  | .not t _ =>
    match t with
    | .trueVal tp => .falseVal tp
    | .falseVal tp => .trueVal tp
    | .not t _ => t
    | .and x y .prop => simp <| .implies x (.not y .prop)
    | .and x y .bool => simp <| .or (.not x .bool) (.not y .bool) .bool
    | .or x y  tp    => simp <| .and (.not x tp) (.not y tp) tp
    | .implies x y => simp <| .and x (.not y .prop) .prop
    | .eq b (.trueVal  .bool) .eqBool => .eq b (.falseVal .bool) .eqBool
    | .eq b (.falseVal .bool) .eqBool => .eq b (.trueVal  .bool) .eqBool
    | .eq b (.not c .bool) .eqBool => simp <| .eq b c .eqBool
    | .eq (.not b .bool) c .eqBool => simp <| .eq b c .eqBool
    | .ne b c .neBool  => .eq b c .eqBool
    | .ite c t f .iteProp =>
        match t, f with
        | eq_true  t, eq_true  f => .ite c (eq_false t) (eq_false f) .iteProp
        | eq_true  t, eq_false f => .ite c (eq_false t) (eq_true  f) .iteProp
        | eq_false t, eq_true  f => .ite c (eq_true t)  (eq_false f) .iteProp
        | eq_false t, eq_false f => .ite c (eq_true t)  (eq_true  f) .iteProp
        | _, _ => v
    | _ => v
  | .and x y tp => Id.run do
      if let .trueVal _ := x then
        return y
      if let .falseVal _ := x then
        return x
      if let .trueVal _ := y then
        return x
      if let .falseVal _ := y then
        return y
      if let .and _xl xr _ := x then
        if xr == y then return x
      if let .and yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      else if isComplement x y then
        return .falseVal tp
      else
        return v
  | .or x y tp => Id.run do
      -- Hardcoded for and-or-imp special case
      if let .and x1 x2 .prop := x then
        if let .implies y1 y2 := y then
          if x1 == y1 then
            return (simp <| .implies x1 (.or x2 y2 .prop))
      if let .falseVal _ := x then
        return y
      if let .trueVal _ := x then
        return x
      if let .falseVal _ := y then
        return x
      if let .trueVal _ := y then
        return y
      if let .or _xl xr _ := x then
        if xr == y then return x
      if let .or yl _yr _ := y then
        if x == yl then return y
      if x == y then
        return x
      if isOrComplement x y tp then
          return .trueVal tp
      pure v
  | .implies x y =>
    match x, y with
    | .trueVal _, y => y
    | .falseVal _, _ => .trueVal .prop
    | _, .trueVal _ => y
    | _, .falseVal _ => simp <| .not x .prop
    | x, y => Id.run <| do
      if x == y then
        return (.trueVal .prop)
      if let eq_true b := x then
        if let eq_false c := y then
          if b == c then
            return y
      if let eq_false b := x then
        if let eq_true c := y then
          if b == c then
            return y
      if let .not x _ := x then
        if x == y then
          return x
      if let .not yn _ := y then
        if x == yn then
          return y
      if let .and a b _ := x then
        return simp <| .implies a <| .implies b y
      return v
  | .eq (.trueVal _) y op =>
    match y with
    | .falseVal _ => .falseVal op.resultType
    | .trueVal _ => .trueVal op.resultType
    | _ =>
      match op with
      | .eqBool => simp <| .eq y (.trueVal .bool) .eqBool
      | .eqProp | .iffProp | .beqBool => y
  | .eq (.falseVal tp) y op =>
    match y with
    | .trueVal  _ => .falseVal op.resultType
    | .falseVal _ => .trueVal  op.resultType
    | _ =>
      match op with
      | .eqBool =>
        simp <| eq_false y
      | _ =>
        simp <| .not y tp
  | .eq x (.trueVal .bool) .eqBool =>
    (match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ => v
    | .decide t => t
    | .not x _   => simp <| eq_false x
    | .and x y _  => simp <| eq_true x &&& eq_true y
    | .or x y _   => simp <| eq_true x ||| eq_true y
    | .eq x y .beqBool => simp <| .eq x y .eqBool
    | .ne x y .bneBool => simp <| .ne x y .neBool
    | .ite c t f op =>
      (match op with
      | .iteBool | .condBool =>
        simp <| .ite (coerceType c .prop) (eq_true t) (eq_true f) .iteProp
      | .diteBool => panic! "expected dite to simplify away."
      | _ => panic! "Unexpected prop when bool expected.")
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected.")
  | .eq x (.trueVal _) _op => x
  | .eq x (.falseVal _) .eqBool  =>
    match x with
    | .trueVal _ | .falseVal _ | .implies _ _ | .boolToProp _ =>
      panic! "Unexpected term."
    | .var _ => v
    | .decide t =>
      simp <| .not t .prop
    | .not x _   =>
      simp <| .eq x (.trueVal .bool) .eqBool
    | .and x y _ => simp <| .implies (eq_true x) (eq_false y)
    | .or  x y _ => simp <| .and (eq_false x) (eq_false y) .prop
    | .eq x y .beqBool => simp <| .not (.eq x y .eqBool) .prop
    | .ne x y .bneBool => simp <| .eq x y .eqBool
    | .ite c t f _ =>
      simp <| .ite (coerceType c .prop) (eq_false t) (eq_false f) .iteProp
    | .eq _ _ _ | .ne _ _ _ =>
        panic! "Unexpected prop when bool expected."
   -- N.B. bool ops other than .eqBool do not change type.
  | .eq x y op => Id.run do
    if let .falseVal tp := y then
      return simp (.not x tp)
    if x == y then
      return (.trueVal op.resultType)
    if isComplement x y then
      return (.falseVal op.resultType)
    if let .beqBool := op then
      if let .eq x1 x2 .beqBool := x then
        if x2 == y then
          return x1
      if let .eq y1 y2 .beqBool := y then
        if x == y1 then
          return y2
    match op with
    | .eqProp | .iffProp | .eqBool =>
      let checks : List (BoolVal → BoolVal → Option BoolVal) := [
        fun x y =>
          if let .and x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp y) (toProp x2)
            else if x2 == y then
              some <| .implies (toProp y) (toProp x1)
            else none
          else none,
        fun x y =>
          if let .and y1 y2 _ := y then
            if x == y1 then
              some <| .implies (toProp x) (toProp y2)
            else if x == y2 then
              some <| .implies (toProp x) (toProp y1)
            else none
          else none,
        fun x y =>
          if let .or x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp x2) (toProp y)
            else if x2 == y then
              some <| .implies (toProp x1) (toProp y)
            else none
          else none,
        fun x y =>
          if let .or y1 y2 _ := y then
            if x == y1 then
              some <| .implies (toProp y2) (toProp x)
            else if x == y2 then
              some <| .implies (toProp y1) (toProp x)
            else none
          else none,
        fun x y =>
          if let .or x1 x2 _ := x then
            if x1 == y then
              some <| .implies (toProp x2) (toProp y)
            else if x2 == y then
              some <| .implies (toProp x1) (toProp y)
            else none
          else none,
        fun x y =>
          if let .implies x1 x2 := x then
            if x2 == y then
              pure <| .or x1 y .prop
            else none
          else none,
        fun x y =>
          if let .implies y1 y2 := y then
            if x == y2 then
              pure <| .or y1 x .prop
            else none
          else none
      ]
      match resolveEq checks x y with
      | some r => return (simp r)
      | none => pure ()
    | _ =>
      pure ()
    match op with
    | .eqProp | .iffProp =>
      match x, y with
      -- The cases below simplify the bool to prop normal forms (b = true, b = false) while
      -- avoiding distributing not over the normal form.
      | eq_true  x, eq_true  y => simp <| .eq x y .eqBool
      | eq_false x, eq_false y => simp <| .eq (~ x) (~ y) .eqBool
      | eq_true  x, eq_false y => simp <| .eq x (~ y) .eqBool
      | eq_false x, eq_true  y => simp <| .eq (~ x) y .eqBool
      | _, _ => iff x y
    | .eqBool =>
      match x, y with
      | .decide x, .decide y => iff x y
      | _, _ => v
    | .beqBool => v
  | .ne x y op => Id.run do
    if let .neBool := op then
      return simp (.not (.eq x y .eqBool) .prop)
    if let .neProp := op then
      return simp (.not (.eq x y .eqProp) .prop)
    if let .trueVal _ := x then
      return simp (~y)
    if let .falseVal _ := x then
      return y
    if let .trueVal _ := y then
      return simp (~x)
    if let .falseVal _ := y then
      return x
    if x == y then
      return .falseVal .bool
    if isComplement x y then
      return .trueVal .bool
    if let .ne y1 y2 .bneBool := y then
      if x == y1 then
        return y2
    pure <|
      match x, y with
      | .ne a b .bneBool, c => simp <| .ne a (.ne b c .bneBool) .bneBool
      | .not x _, .not y _ =>  simp <| .ne x y .bneBool
      | _, _ => v
  | .ite c t f op => Id.run do
    if let .trueVal _ := c then
      return t
    if let .falseVal _ := c then
      return f
    if let .not c _ := c then
      return simp <| .ite c f t op
    if let .falseVal tp := t then
      return simp <| (~(coerceType c tp)) &&& f
    if let .falseVal tp := f then
      return simp <| (coerceType c tp) &&& t
    -- NB. The patterns where a branch is true are
    -- intentionally after branches with a
    -- false because we prefer to introduce conjunction
    -- over disjunction/implies when overlapping.
    if let .trueVal _ := t then
      let r :=
        match op with
        | .iteBool => simp <| toBool c ||| f
        | .iteProp => simp <| .implies (~c) f
        | .condBool => simp <|  c ||| f
        | _ => v
      return r
    if let .trueVal _ := f then
      let r :=
        match op with
        | .iteBool  => simp <| ~(toBool c) ||| t
        | .iteProp  => simp <| .implies c t
        | .condBool => simp <| ~c ||| t
        | _ => v
      return r
    if t == f then
      return t
    let matchProp c x :=
          match op with
          | .iteBool =>
              if let .decide x := x then
                if c == x then
                  some (toBool c)
                else
                  none
              else
                none
          | .iteProp | .condBool => if c == x then some c else none
          | _ => none
    if let some c := matchProp c t then
      let r :=
        match f.typeOf with
        | .bool => simp <| c ||| f
        | .prop => simp <| .implies (.not c .prop) f
      return r
    if let some c := matchProp c f then
      return simp <| c &&& t
    let op := match op with
              | .diteProp => .iteProp
              | .diteBool => .iteBool
              | _ => op
    .ite c t f op
  | .trueVal _ | .falseVal _ | .var _ => v
end
set_option profiler false

end BoolVal

def vars : List (BoolType × CoreM Command) := [
    (.bool, `(variable (b : Bool))),
    (.prop, `(variable (p : Prop) [Decidable p]))
  ]

section
open BoolVal BoolType

def trueOp  (tp : BoolType) := mkOp [] tp fun _ => trueVal  tp
def falseOp (tp : BoolType) := mkOp [] tp fun _ => falseVal tp
def boolToPropOp := mkOp [.bool] prop fun a => boolToProp (a[0]!)
def propToBoolOp := mkOp [prop] .bool fun a => BoolVal.decide (a[0]!)
def notOp (tp : BoolType) := mkOp [tp] tp fun a => not (a[0]!) tp
def andOp (tp : BoolType) := mkOp [tp, tp] tp fun a => and (a[0]!) (a[1]!) tp
def orOp  (tp : BoolType) := mkOp [tp, tp] tp fun a => or  (a[0]!) (a[1]!) tp
def impliesOp := mkOp [.prop, .prop] prop fun a => implies  (a[0]!) (a[1]!)
def eqOp (op : EqOp) := mkOp [op.argType, op.argType] op.resultType fun a => eq (a[0]!) (a[1]!) op
def neOp (op : NeOp) := mkOp [op.argType, op.argType] op.resultType fun a => ne (a[0]!) (a[1]!) op
def iteOp (op : IteOp) :=
  let rtp := op.resultType
  mkOp [op.condType, rtp, rtp] rtp fun a => ite (a[0]!) (a[1]!) (a[2]!) op

end

instance : GenTerm BoolVal BoolType where
  mkVar := BoolVal.var
  render := BoolVal.render

syntax:lead (name := boolTestElab) "#boolTest" : command

@[command_elab boolTestElab]
def elabBoolTest : CommandElab := fun _stx => do
  let baseOps := [
      trueOp  .bool,  trueOp .prop,
      falseOp .bool, falseOp .prop,
      boolToPropOp, propToBoolOp,
      notOp .bool, notOp .prop,
      andOp .bool, andOp .prop,
      orOp .bool,  orOp .prop,
      impliesOp
  ]
  let eqOps := [ eqOp .eqProp, eqOp .eqBool, eqOp .iffProp, eqOp .beqBool ]
  let neOps := [ neOp .neProp, neOp .neBool, neOp .bneBool ]
  let iteOps := [
    iteOp .iteProp, iteOp .iteBool,
    --iteOp .diteProp,  iteOp .diteBool,
    iteOp .condBool
  ]
  let types := [.prop, .bool]
  let ops := baseOps ++ eqOps ++ neOps ++ iteOps
  let stats : GenStats := { maxTermSize := 7, maxDepth := 3, maxVarCount := 2 }
  testNormalForms types ops vars BoolVal.simp stats

set_option maxHeartbeats 10000000
--set_option profiler true
--set_option profiler.threshold 1
set_option trace.Test.normalforms true
#boolTest
