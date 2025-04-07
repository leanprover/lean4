/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega.Constraint
import Lean.Elab.Tactic.Omega.OmegaM
import Lean.Elab.Tactic.Omega.MinNatAbs

namespace Lean.Elab.Tactic.Omega

initialize Lean.registerTraceClass `omega

open Lean (Expr)
open Lean Meta Omega

open Lean in
instance : ToExpr LinearCombo where
  toExpr lc :=
    (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

open Lean in
instance : ToExpr Constraint where
  toExpr s :=
    (Expr.const ``Constraint.mk []).app (toExpr s.lowerBound) |>.app (toExpr s.upperBound)
  toTypeExpr := .const ``Constraint []

/--
A delayed proof that a constraint is satisfied at the atoms.
-/
abbrev Proof : Type := OmegaM Expr

/--
Our internal representation of an argument "justifying" that a constraint holds on some coefficients.
We'll use this to construct the proof term once a contradiction is found.
-/
inductive Justification : Constraint → Coeffs → Type
  /--
  `Problem.assumptions[i]` generates a proof that `s.sat' coeffs atoms`
  -/
  | assumption (s : Constraint) (x : Coeffs) (i : Nat) : Justification s x
  /-- The result of `tidy` on another `Justification`. -/
  | tidy (j : Justification s c) : Justification (tidyConstraint s c) (tidyCoeffs s c)
  /-- The result of `combine` on two `Justifications`. -/
  | combine {s t c} (j : Justification s c) (k : Justification t c) : Justification (s.combine t) c
  /-- A linear `combo` of two `Justifications`. -/
  | combo {s t x y} (a : Int) (j : Justification s x) (b : Int) (k : Justification t y) :
    Justification (Constraint.combo a s b t) (Coeffs.combo a x b y)
  /--
  The justification for the constraint constructed using "balanced mod" while
  eliminating an equality.
  -/
  | bmod (m : Nat) (r : Int) (i : Nat) {x} (j : Justification (.exact r) x) :
      Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)

/-- Wrapping for `Justification.tidy` when `tidy?` is nonempty. -/
nonrec def Justification.tidy? (j : Justification s c) : Option (Σ s' c', Justification s' c') :=
  match tidy? (s, c) with
  | some _ => some ⟨_, _, tidy j⟩
  | none => none

namespace Justification

private def bullet (s : String) := "• " ++ s.replace "\n" "\n  "

/-- Print a `Justification` as an indented tree structure. -/
def toString : Justification s x → String
  | assumption _ _ i => s!"{x} ∈ {s}: assumption {i}"
  | @tidy s' x' j =>
    if s == s' && x == x' then j.toString else s!"{x} ∈ {s}: tidying up:\n" ++ bullet j.toString
  | combine j k =>
    s!"{x} ∈ {s}: combination of:\n" ++ bullet j.toString ++ "\n" ++ bullet k.toString
  | combo a j b k =>
    s!"{x} ∈ {s}: {a} * x + {b} * y combo of:\n" ++ bullet j.toString ++ "\n" ++ bullet k.toString
  | bmod m _ i j =>
    s!"{x} ∈ {s}: bmod with m={m} and i={i} of:\n" ++ bullet j.toString

instance : ToString (Justification s x) where toString := toString

open Lean

/-- Construct the proof term associated to a `tidy` step. -/
def tidyProof (s : Constraint) (x : Coeffs) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``tidy_sat []) (toExpr s) (toExpr x) v prf

/-- Construct the proof term associated to a `combine` step. -/
def combineProof (s t : Constraint) (x : Coeffs) (v : Expr) (ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' []) (toExpr s) (toExpr t) (toExpr x) v ps pt

/-- Construct the proof term associated to a `combo` step. -/
def comboProof (s t : Constraint) (a : Int) (x : Coeffs) (b : Int) (y : Coeffs)
    (v : Expr) (px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat' []) (toExpr s) (toExpr t) (toExpr a) (toExpr x) (toExpr b) (toExpr y)
    v px py

/-- Construct the proof term associated to a `bmod` step. -/
def bmodProof (m : Nat) (r : Int) (i : Nat) (x : Coeffs) (v : Expr) (w : Expr) : MetaM Expr := do
  let m := toExpr m
  let r := toExpr r
  let i := toExpr i
  let x := toExpr x
  let h ← mkDecideProof (mkApp4 (.const ``LE.le [.zero]) (.const ``Nat []) (.const ``instLENat [])
    (.app (.const ``Coeffs.length []) x) i)
  let lhs := mkApp2 (.const ``Coeffs.get []) v i
  let rhs := mkApp3 (.const ``bmod_div_term []) m x v
  let p ← mkEqReflWithExpectedType lhs rhs
  return mkApp8 (.const ``bmod_sat []) m r i x v h p w

-- TODO could we increase sharing in the proof term here?

/-- Constructs a proof that `s.sat' c v = true` -/
def proof (v : Expr) (assumptions : Array Proof) : Justification s c → Proof
  | assumption s c i => assumptions[i]!
  | @tidy s c j => return tidyProof s c v (← proof v assumptions j)
  | @combine s t c j k =>
    return combineProof s t c v (← proof v assumptions j) (← proof v assumptions k)
  | @combo s t x y a j b k =>
    return comboProof s t a x b y v (← proof v assumptions j) (← proof v assumptions k)
  | @bmod m r i x j => do bmodProof m r i x v (← proof v assumptions j)

end Justification

/-- A `Justification` bundled together with its parameters. -/
structure Fact where
  /-- The coefficients of a constraint. -/
  coeffs : Coeffs
  /-- The constraint. -/
  constraint : Constraint
  /-- The justification of a derived fact. -/
  justification : Justification constraint coeffs

namespace Fact

instance : ToString Fact where
  toString f := toString f.justification

/-- `tidy`, implemented on `Fact`. -/
def tidy (f : Fact) : Fact :=
  match f.justification.tidy? with
  | some ⟨constraint, coeffs, justification⟩ => { coeffs, constraint, justification }
  | none => f

/-- `combo`, implemented on `Fact`. -/
def combo (a : Int) (f : Fact) (b : Int) (g : Fact) : Fact :=
  { coeffs := .combo a f.coeffs b g.coeffs
    constraint := .combo a f.constraint b g.constraint
    justification := .combo a f.justification b g.justification }

end Fact

/--
A `omega` problem.

This is a hybrid structure:
it contains both `Expr` objects giving proofs of the "ground" assumptions
(or rather continuations which will produce the proofs when needed)
and internal representations of the linear constraints that we manipulate in the algorithm.

While the algorithm is running we do not synthesize any new `Expr` proofs: proof extraction happens
only once we've found a contradiction.
-/
structure Problem where
  /-- The ground assumptions that the algorithm starts from. -/
  assumptions : Array Proof := ∅
  /-- The number of variables in the problem. -/
  numVars : Nat := 0
  /-- The current constraints, indexed by their coefficients. -/
  constraints : Std.HashMap Coeffs Fact := ∅
  /--
  The coefficients for which `constraints` contains an exact constraint (i.e. an equality).
  -/
  equalities : Std.HashSet Coeffs := ∅
  /--
  Equations that have already been used to eliminate variables,
  along with the variable which was removed, and its coefficient (either `1` or `-1`).
  The earlier elements are more recent,
  so if these are being reapplied it is essential to use `List.foldr`.
  -/
  eliminations : List (Fact × Nat × Int) := []
  /-- Whether the problem is possible. -/
  possible : Bool := true
  /-- If the problem is impossible, then `proveFalse?` will contain a proof of `False`. -/
  proveFalse? : Option Proof := none
  /-- Invariant between `possible` and `proveFalse?`. -/
  proveFalse?_spec : possible || proveFalse?.isSome := by rfl
  /--
  If we have found a contradiction,
  `explanation?` will contain a human readable account of the deriviation.
  -/
  explanation? : Thunk String := ""

namespace Problem

/-- Check if a problem has no constraints. -/
def isEmpty (p : Problem) : Bool := p.constraints.isEmpty

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, ⟨_, cst, _⟩⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"

open Lean in
/--
Takes a proof that `s.sat' x v` for some `s` such that `s.isImpossible`,
and constructs a proof of `False`.
-/
def proveFalse {s x} (j : Justification s x) (assumptions : Array Proof) : Proof := do
  let v := ← atomsCoeffs
  let prf ← j.proof v assumptions
  let x := toExpr x
  let s := toExpr s
  let impossible ←
    mkDecideProof (← mkEq (mkApp (.const ``Constraint.isImpossible []) s) (.const ``true []))
  return mkApp5 (.const ``Constraint.not_sat'_of_isImpossible []) s impossible x v prf

/--
Insert a constraint into the problem,
without checking if there is already a constraint for these coefficients.
-/
def insertConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if s.isImpossible then
      { p with
        possible := false
        proveFalse? := some (proveFalse j p.assumptions)
        explanation? := Thunk.mk fun _ => j.toString
        proveFalse?_spec := rfl }
    else
      { p with
        numVars := max p.numVars x.length
        constraints := p.constraints.insert x f
        proveFalse?_spec := p.proveFalse?_spec
        equalities :=
        if f.constraint.isExact then
          p.equalities.insert x
        else
          p.equalities }

/--
Add a constraint into the problem,
combining it with any existing constraints for the same coefficients.
-/
def addConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if p.possible then
      match p.constraints[x]? with
      | none =>
        match s with
        | .trivial => p
        | _ => p.insertConstraint f
      | some ⟨x', t, k⟩ =>
        if h : x = x' then
          let r := s.combine t
          if r = t then
            -- No need to overwrite the existing fact
            -- with the same fact with a more complicated justification
            p
          else
            if r = s then
              -- The new constraint is strictly stronger, no need to combine with the old one:
              p.insertConstraint ⟨x, s, j⟩
            else
              p.insertConstraint ⟨x, s.combine t, j.combine (h ▸ k)⟩
        else
          p -- unreachable
    else
      p

/--
Walk through the equalities, finding either the first equality with minimal coefficient `±1`,
or otherwise the equality with minimal `(r.minNatAbs, r.maxNatAbs)` (ordered lexicographically).

Returns the coefficients of the equality, along with the value of `minNatAbs`.

Although we don't need to run a termination proof here, it's nevertheless important that we use this
ordering so the algorithm terminates in practice!
-/
def selectEquality (p : Problem) : Option (Coeffs × Nat) :=
  p.equalities.fold (init := none) fun
  | none, c => (c, c.minNatAbs)
  | some (r, m), c =>
    if 2 ≤ m then
      let m' := c.minNatAbs
      if (m' < m || m' = m && c.maxNatAbs < r.maxNatAbs) then
        (c, m')
      else
        (r, m)
    else
      (r, m)

/--
If we have already solved some equalities, apply those to some new `Fact`.
-/
def replayEliminations (p : Problem) (f : Fact) : Fact :=
  p.eliminations.foldr (init := f) fun (f, i, s) g =>
    match Coeffs.get g.coeffs i with
    | 0 => g
    | y => Fact.combo (-1 * s * y) f 1 g

/--
Solve an "easy" equality, i.e. one with a coefficient that is `±1`.

After solving, the variable will have been eliminated from all constraints.
-/
def solveEasyEquality (p : Problem) (c : Coeffs) : Problem :=
  let i := c.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.get i |> Int.sign
  match p.constraints[c]? with
  | some f =>
    let init :=
    { assumptions := p.assumptions
      eliminations := (f, i, sign) :: p.eliminations }
    p.constraints.fold (init := init) fun p' coeffs g =>
      match Coeffs.get coeffs i with
      | 0 =>
        p'.addConstraint g
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (Fact.combo k f 1 g).tidy
  | _ => p -- unreachable

open Lean in
/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coeffs) : OmegaM Problem :=
  match p.constraints[c]? with
  | some ⟨_, ⟨some r, some r'⟩, j⟩ => do
    let m := c.minNatAbs + 1
    -- We have to store the valid value of the newly introduced variable in the atoms.
    let x := mkApp3 (.const ``bmod_div_term []) (toExpr m) (toExpr c) (← atomsCoeffs)
    let (i, facts?) ← lookup x
    if hr : r' = r then
      match facts? with
      | none => throwError "When solving hard equality, new atom had been seen before!"
      | some facts => if ! facts.isEmpty then
        throwError "When solving hard equality, there were unexpected new facts!"
      return p.addConstraint { coeffs := _, constraint := _, justification := (hr ▸ j).bmod m r i }
    else
      throwError "Invalid constraint, expected an equation." -- unreachable
  | _ =>
    return p -- unreachable

/--
Solve an equality, by deciding whether it is easy (has a `±1` coefficient) or hard,
and delegating to the appropriate function.
-/
def solveEquality (p : Problem) (c : Coeffs) (m : Nat) : OmegaM Problem :=
  if m = 1 then
    return p.solveEasyEquality c
  else
    p.dealWithHardEquality c

/-- Recursively solve all equalities. -/
partial def solveEqualities (p : Problem) : OmegaM Problem :=
  if p.possible then
    match p.selectEquality with
    | some (c, m) => do (← p.solveEquality c m).solveEqualities
    | none => return p
  else return p

open Constraint

open Lean in
/-- Constructing the proof term for `addInequality`. -/
def addInequality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addInequality_sat []) (toExpr c) (toExpr x) (← atomsCoeffs) (← p)

open Lean in
/-- Constructing the proof term for `addEquality`. -/
def addEquality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addEquality_sat []) (toExpr c) (toExpr x) (← atomsCoeffs) (← p)

/--
Helper function for adding an inequality of the form `const + Coeffs.dot coeffs atoms ≥ 0`
to a `Problem`.

(This is only used while initializing a `Problem`. During elimination we use `addConstraint`.)
-/
-- We are given `prf? : const + Coeffs.dot coeffs atoms ≥ 0`,
-- and need to transform this to `Coeffs.dot coeffs atoms ≥ -const`.
def addInequality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
  let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
  let i := p.assumptions.size
  let p' := { p with assumptions := p.assumptions.push (addInequality_proof const coeffs prf) }
  let f : Fact :=
  { coeffs
    constraint := { lowerBound := some (-const), upperBound := none }
    justification := .assumption _ _ i }
  let f := p.replayEliminations f
  let f := f.tidy
  p'.addConstraint f

/--
Helper function for adding an equality of the form `const + Coeffs.dot coeffs atoms = 0`
to a `Problem`.

(This is only used while initializing a `Problem`. During elimination we use `addConstraint`.)
-/
def addEquality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
  let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
  let i := p.assumptions.size
  let p' := { p with assumptions := p.assumptions.push (addEquality_proof const coeffs prf) }
  let f : Fact :=
  { coeffs
    constraint := { lowerBound := some (-const), upperBound := some (-const) }
    justification := .assumption _ _ i }
  let f := p.replayEliminations f
  let f := f.tidy
  p'.addConstraint f

/-- Folding `addInequality` over a list. -/
def addInequalities (p : Problem) (ineqs : List (Int × Coeffs × Option Proof)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addInequality const coeffs prf?

/-- Folding `addEquality` over a list. -/
def addEqualities (p : Problem) (eqs : List (Int × Coeffs × Option Proof)) : Problem :=
  eqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addEquality const coeffs prf?

/-- Representation of the data required to run Fourier-Motzkin elimination on a variable. -/
structure FourierMotzkinData where
  /-- Which variable is being eliminated. -/
  var : Nat
  /-- The "irrelevant" facts which do not involve the target variable. -/
  irrelevant : List Fact := []
  /--
  The facts which give a lower bound on the target variable,
  and the coefficient of the target variable in each.
  -/
  lowerBounds : List (Fact × Int) := []
  /--
  The facts which give an upper bound on the target variable,
  and the coefficient of the target variable in each.
  -/
  upperBounds : List (Fact × Int) := []
  /--
  Whether the elimination would be exact, because all of the lower bound coefficients are `±1`.
  -/
  lowerExact : Bool := true
  /--
  Whether the elimination would be exact, because all of the upper bound coefficients are `±1`.
  -/
  upperExact : Bool := true
deriving Inhabited

instance : ToString FourierMotzkinData where
  toString d :=
    let irrelevant := d.irrelevant.map fun ⟨x, s, _⟩ => s!"{x} ∈ {s}"
    let lowerBounds := d.lowerBounds.map fun ⟨⟨x, s, _⟩, _⟩ => s!"{x} ∈ {s}"
    let upperBounds := d.upperBounds.map fun ⟨⟨x, s, _⟩, _⟩ => s!"{x} ∈ {s}"
    s!"Fourier-Motzkin elimination data for variable {d.var}\n"
      ++ s!"• irrelevant: {irrelevant}\n"
      ++ s!"• lowerBounds: {lowerBounds}\n"
      ++ s!"• upperBounds: {upperBounds}"

/-- Is a Fourier-Motzkin elimination empty (i.e. there are no relevant constraints). -/
def FourierMotzkinData.isEmpty (d : FourierMotzkinData) : Bool :=
  d.lowerBounds.isEmpty && d.upperBounds.isEmpty
/-- The number of new constraints that would be introduced by Fourier-Motzkin elimination. -/
def FourierMotzkinData.size (d : FourierMotzkinData) : Nat :=
  d.lowerBounds.length * d.upperBounds.length
/-- Is the Fourier-Motzkin elimination known to be exact? -/
def FourierMotzkinData.exact (d : FourierMotzkinData) : Bool := d.lowerExact || d.upperExact

/-- Prepare the Fourier-Motzkin elimination data for each variable. -/
-- TODO we could short-circuit here, if we find one with `size = 0`.
def fourierMotzkinData (p : Problem) : Array FourierMotzkinData := Id.run do
  let n := p.numVars
  let mut data : Array FourierMotzkinData :=
    (List.range p.numVars).foldl (fun a i => a.push { var := i}) #[]
  for (_, f@⟨xs, s, _⟩) in p.constraints do
    for i in [0:n] do
      let x := Coeffs.get xs i
      data := data.modify i fun d =>
        if x = 0 then
          { d with irrelevant := f :: d.irrelevant }
        else Id.run do
          let s' := s.scale x
          let mut d' := d
          if s'.lowerBound.isSome then
            d' := { d' with
              lowerBounds := (f, x) :: d'.lowerBounds
              lowerExact := d'.lowerExact && x.natAbs = 1 }
          if s'.upperBound.isSome then
            d' := { d' with
              upperBounds := (f, x) :: d'.upperBounds
              upperExact := d'.upperExact && x.natAbs = 1 }
          return d'
  return data

/--
Decides which variable to run Fourier-Motzkin elimination on, and returns the associated data.

We prefer eliminations which introduce no new inequalities, or otherwise exact eliminations,
and break ties by the number of new inequalities introduced.
-/
def fourierMotzkinSelect (data : Array FourierMotzkinData) : MetaM FourierMotzkinData := do
  let data := data.filter fun d => ¬ d.isEmpty
  trace[omega] "Selecting variable to eliminate from (idx, size, exact) triples:\n\
    {data.map fun d => (d.var, d.size, d.exact)}"
  let mut bestIdx := 0
  let mut bestSize := data[0]!.size
  let mut bestExact := data[0]!.exact
  if bestSize = 0 then
    trace[omega] "Selected variable {data[0]!.var}."
    return data[0]!
  for h : i in [1:data.size] do
    let exact := data[i].exact
    let size := data[i].size
    if size = 0 || !bestExact && exact || (bestExact == exact) && size < bestSize then
      if size = 0 then
        trace[omega] "Selected variable {data[i].var}"
        return data[i]
      bestIdx := i
      bestExact := exact
      bestSize := size
  trace[omega] "Selected variable {data[bestIdx]!.var}."
  return data[bestIdx]!

/--
Run Fourier-Motzkin elimination on one variable.
-/
-- This is only in MetaM to enable tracing.
def fourierMotzkin (p : Problem) : MetaM Problem := do
  let data := p.fourierMotzkinData
  -- Now perform the elimination.
  let ⟨_, irrelevant, lower, upper, _, _⟩ ← fourierMotzkinSelect data
  let mut r : Problem := { assumptions := p.assumptions, eliminations := p.eliminations }
  for f in irrelevant do
    r := r.insertConstraint f
  for ⟨f, b⟩ in lower do
    for ⟨g, a⟩ in upper do
      r := r.addConstraint (Fact.combo a f (-b) g).tidy
  return r

mutual

/--
Run the `omega` algorithm (for now without dark and grey shadows!) on a problem.
-/
partial def runOmega (p : Problem) : OmegaM Problem := do
  trace[omega] "Running omega on:\n{p}"
  if p.possible then
    let p' ← p.solveEqualities
    elimination p'
  else
    return p

/-- As for `runOmega`, but assuming the first round of solving equalities has already happened. -/
partial def elimination (p : Problem) : OmegaM Problem :=
  if p.possible then
    if p.isEmpty then
      return p
    else do
      trace[omega] "Running Fourier-Motzkin elimination on:\n{p}"
      runOmega (← p.fourierMotzkin)
  else
    return p

end

end Problem

end Lean.Elab.Tactic.Omega
