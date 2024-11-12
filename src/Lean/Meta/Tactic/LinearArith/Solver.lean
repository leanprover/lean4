/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Ord
import Init.Data.Array.DecidableEq
import Lean.Data.Rat

namespace Lean.Meta.Linear

structure Var where
  id : Nat
  deriving Inhabited, Ord, DecidableEq, Repr

instance : LT Var where
  lt a b := a.id < b.id

instance (a b : Var) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.id < b.id))

structure Assignment where
  val : Array Rat := #[]
  deriving Inhabited

abbrev Assignment.size (a : Assignment) : Nat :=
  a.val.size

abbrev Assignment.get? (a : Assignment) (x : Var) : Option Rat :=
  if h : x.id < a.size then
    some (a.val[x.id])
  else
    none

abbrev Assignment.push (a : Assignment) (v : Rat) : Assignment :=
  { a with val := a.val.push v }

abbrev Assignment.take (a : Assignment) (newSize : Nat) : Assignment :=
  { a with val := a.val.take newSize }

structure Poly where
  val : Array (Int × Var)
  deriving Inhabited, Repr, DecidableEq

abbrev Poly.size (e : Poly) : Nat :=
  e.val.size

abbrev Poly.getMaxVarCoeff (e : Poly) : Int :=
  e.val.back!.1

abbrev Poly.getMaxVar (e : Poly) : Var :=
  e.val.back!.2

abbrev Poly.get (e : Poly) (i : Fin e.size) : Int × Var :=
  e.val[i]

def Poly.scale (d : Int) (e : Poly) : Poly :=
  { e with val := e.val.map fun (c, x) => (c*d, x) }

def Poly.add (e₁ e₂ : Poly) : Poly :=
  let rec go (i₁ i₂ : Nat) (r : Array (Int × Var)) : Poly :=
    if h₁ : i₁ < e₁.size then
      if h₂ : i₂ < e₂.size then
        let (c₁, x₁) := e₁.get ⟨i₁, h₁⟩
        let (c₂, x₂) := e₂.get ⟨i₂, h₂⟩
        if x₁ = x₂ then
           if c₁ + c₂ = 0 then
             go (i₁+1) (i₂+1) r
           else
             go (i₁+1) (i₂+1) (r.push (c₁+c₂, x₁))
        else if x₁ < x₂ then
          go (i₁+1) i₂ (r.push (c₁, x₁))
        else
          go i₁ (i₂+1) (r.push (c₂, x₂))
      else
        go (i₁+1) i₂ (r.push (e₁.get ⟨i₁, h₁⟩))
    else
      if h₂ : i₂ < e₂.size then
        go i₁ (i₂+1) (r.push (e₂.get ⟨i₂, h₂⟩))
      else
        { val := r }
    termination_by (e₁.size - i₁, e₂.size - i₂)
    decreasing_by all_goals decreasing_with decreasing_trivial_pre_omega
  go 0 0 #[]

def Poly.combine (d₁ : Int) (e₁ : Poly) (d₂ : Int) (e₂ : Poly) : Poly :=
  let rec go (i₁ i₂ : Nat) (r : Array (Int × Var)) : Poly :=
    if h₁ : i₁ < e₁.size then
      let (c₁, x₁) := e₁.get ⟨i₁, h₁⟩
      if h₂ : i₂ < e₂.size then
        let (c₂, x₂) := e₂.get ⟨i₂, h₂⟩
        if x₁ = x₂ then
           let c := c₁*d₁ + c₂*d₂
           if c = 0 then
             go (i₁+1) (i₂+1) r
           else
             go (i₁+1) (i₂+1) (r.push (c, x₁))
        else if x₁ < x₂ then
          go (i₁+1) i₂ (r.push (d₁*c₁, x₁))
        else
          go i₁ (i₂+1) (r.push (d₂*c₂, x₂))
      else
        go (i₁+1) i₂ (r.push (d₁*c₁, x₁))
    else
      if h₂ : i₂ < e₂.size then
        let (c₂, x₂) := e₂.get ⟨i₂, h₂⟩
        go i₁ (i₂+1) (r.push (d₂*c₂, x₂))
      else
        { val := r }
    termination_by (e₁.size - i₁, e₂.size - i₂)
    decreasing_by all_goals decreasing_with decreasing_trivial_pre_omega
  go 0 0 #[]

def Poly.eval? (e : Poly) (a : Assignment) : Option Rat := Id.run do
  let mut r := 0
  for (c, x) in e.val do
    if let some v := a.get? x then
      r := r + c*v
    else
      return none
  return r

structure AssumptionId where
  id : Nat := 0
  deriving Inhabited, DecidableEq, Repr

inductive Justification where
  | combine (c₁ : Int) (j₁ : Justification) (c₂ : Int) (j₂ : Justification)
  | assumption (id : AssumptionId)
  deriving Inhabited, DecidableEq, BEq, Repr

inductive CnstrKind where
  | eq | div | lt | le
  deriving Inhabited, DecidableEq, BEq, Repr

structure Cnstr where
  kind : CnstrKind
  lhs  : Poly
  rhs  : Int
  jst  : Justification
  deriving Inhabited, DecidableEq, BEq, Repr

abbrev Cnstr.isStrict (c : Cnstr) : Bool :=
  c.kind matches CnstrKind.lt

def Cnstr.getBound (c : Cnstr) (a : Assignment) : Rat := Id.run do
  let mut r : Rat := c.rhs
  -- The maximal variable is in the last position
  for (c, x) in c.lhs.val[:c.lhs.val.size-1] do
    if let some v := a.get? x then
      r := r - c*v
    else
      unreachable!
  let k := c.lhs.val.back!.1
  return r / k

def Cnstr.isUnsat (c : Cnstr) (a : Assignment) : Bool :=
  if let some v := c.lhs.eval? a then
    match c.kind with
    | CnstrKind.eq => !(v == c.rhs)
    | CnstrKind.lt => !(v < c.rhs)
    | CnstrKind.le => !(v <= c.rhs)
    | CnstrKind.div => unreachable! -- TODO
  else
    false

def getBestBound? (cs : Array Cnstr) (a : Assignment) (isLower isInt : Bool) : Option (Rat × Cnstr) :=
  let adjust (v : Rat) :=
    if isInt then if isLower then (v.ceil : Rat) else v.floor else v
  if h : 0 < cs.size then
    let c0 := cs[0]
    let b  := adjust <| c0.getBound a
    some <| cs[1:].foldl (init := (b, c0)) fun r c =>
      let b' := adjust <| c.getBound a
      if isLower then
        if b' > r.1 then (b', c) else r
      else
        if b' < r.1 then (b', c) else r
  else
    none

inductive Result where
  | unsat (j : Justification)
  | unsupported
  | timeout
  | sat (a : Assignment)

structure Context where
  int : Array Bool

structure State where
  lowers      : Array (Array Cnstr)
  uppers      : Array (Array Cnstr)
  int         : Array Bool
  assignment  : Assignment := {} -- partial assignment
  deriving Inhabited

abbrev State.getNumVars (s : State) : Nat := s.lowers.size

abbrev State.currVar (s : State) : Nat := s.assignment.size

abbrev State.getBestLowerBound? (s : State) : Option (Rat × Cnstr) :=
  getBestBound? s.lowers[s.currVar]! s.assignment true s.int[s.currVar]!

abbrev State.getBestUpperBound? (s : State) : Option (Rat × Cnstr) :=
  getBestBound? s.uppers[s.currVar]! s.assignment false s.int[s.currVar]!

abbrev State.assignCurr (s : State) (v : Rat) : State :=
  { s with assignment := s.assignment.push v }

def pickAssignment? (lower : Rat) (lowerIsStrict : Bool) (upper : Rat) (upperIsStrict : Bool) : Option Rat :=
  if lower == upper then
    if lowerIsStrict || upperIsStrict then none else some lower
  else if lower < upper then
    if lowerIsStrict then
      let c := if lower.isInt then lower + 1 else lower.ceil
      if c < upper then some c else some ((lower + upper) / 2)
    else
      some lower
  else
    none

def resolve (s : State) (cl : Cnstr) (cu : Cnstr) : Sum Result State :=
  let kl : Int := - cl.lhs.getMaxVarCoeff
  let ku : Int := cu.lhs.getMaxVarCoeff
  -- Both `kl` and `ku` must be positive
  let lhs := Poly.combine ku cl.lhs kl cu.lhs
  -- TODO: normalize coefficients
  let rhs := ku * cl.rhs + kl * cu.rhs
  let c   := {
    lhs, rhs,
    kind := if cl.isStrict || cu.isStrict then CnstrKind.lt else CnstrKind.le
    jst  := Justification.combine kl cl.jst ku cu.jst
    : Cnstr }
  if !c.isUnsat s.assignment then
    -- TODO: the naive resolution procedure above may fail for integer constraints
    Sum.inl Result.unsupported
  else if lhs.size == 0 then
    Sum.inl <| Result.unsat c.jst
  else
    let maxVarIdx := c.lhs.getMaxVar.id
    match s with -- Hack: we avoid { s with ... } to make sure we get a destructive update
    | { lowers, uppers, int, assignment, } =>
      let assignment := assignment.take maxVarIdx
      if c.lhs.getMaxVarCoeff < 0 then
        let lowers := lowers.modify maxVarIdx (·.push c)
        Sum.inr { lowers, uppers, int, assignment }
      else
        let uppers := uppers.modify maxVarIdx (·.push c)
        Sum.inr { lowers, uppers, int, assignment }

def solve (n : Nat) (s : State) : Result :=
  match n with
  | 0   => Result.timeout
  | n+1 =>
    let i := s.currVar
    if i = s.getNumVars then
      Result.sat s.assignment -- all variables have been assigned
    else
      match s.getBestLowerBound?, s.getBestUpperBound? with
      | none,         none         => solve n <| s.assignCurr 0
      | some (l, cl), none         => solve n <| s.assignCurr (if cl.isStrict then l.ceil + 1 else l.ceil)
      | none,         some (u, cu) => solve n <| s.assignCurr (if cu.isStrict then u.floor - 1 else u.floor)
      | some (l, cl), some (u, cu) =>
        match pickAssignment? l cl.isStrict u cu.isStrict with
        | some v => solve n <| s.assignCurr v
        | none => match resolve s cl cu with
          | Sum.inl r => r
          | Sum.inr s => solve n s

end Lean.Meta.Linear
