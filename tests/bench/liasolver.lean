/-
Linear Diophantine equation solver

Author: Marc Huisinga
-/

import Lean.Data.HashMap

open Lean

namespace Int

  def roundedDiv (a b : Int) : Int := Id.run <| do
    if b = 0 then
      return 0
    let mut div := a / b
    let rest := a % b
    -- This determines how we should adjust the divisor.
    -- The extra logic is to preserve tie-breaking behavior from
    -- a time when div used T-rounding
    if a ≥ 0 then
      if 2*rest ≥ b.natAbs then
        div := div + (if b ≥ 0 then 1 else -1)
    else
      if 2*rest > b.natAbs then
        div := div + (if b >= 0 then 1 else -1)
    return div

  def mod' (a b : Int) : Int :=
    a - b*(a.roundedDiv b)

end Int

namespace Lean.AssocList

  def map (f : α → β → δ) : AssocList α β → AssocList α δ
    | AssocList.nil        => AssocList.nil
    | AssocList.cons k v t => AssocList.cons k (f k v) (map f t)

  def filter (p : α → β → Bool) : AssocList α β → AssocList α β
    | AssocList.nil        => AssocList.nil
    | AssocList.cons k v t =>
      if p k v then
        AssocList.cons k v (filter p t)
      else
        filter p t

end Lean.AssocList

namespace Lean.HashMap

  variable [BEq α] [Hashable α]

  @[inline] protected def forIn {δ : Type w} {m : Type w → Type w'} [Monad m]
    (as : HashMap α β) (init : δ) (f : (α × β) → δ → m (ForInStep δ)) : m δ := do
    as.val.buckets.val.forIn init fun bucket acc => do
      let (done, v) ← bucket.forIn (false, acc) fun v (_, acc) => do
        let r ← f v acc
        match r with
        | ForInStep.done r' =>
          return ForInStep.done (true, r')
        | ForInStep.yield r' =>
          return ForInStep.yield (false, r')
      if done then
        return ForInStep.done v
      else
        return ForInStep.yield v

  instance : ForIn m (HashMap α β) (α × β) where
    forIn := HashMap.forIn

  def modify! [Inhabited β] (xs : HashMap α β) (k : α) (f : β → β) : HashMap α β :=
    let v := xs.find! k
    xs.erase k |>.insert k (f v)

  def any (xs : HashMap α β) (p : α → β → Bool) : Bool := Id.run <| do
    for (k, v) in xs do
      if p k v then
        return true
    return false

  def mapValsM [Monad m] (f : β → m γ) (xs : HashMap α β) : m (HashMap α γ) :=
    mkHashMap (capacity := xs.size) |> xs.foldM fun acc k v => return acc.insert k (←f v)

  def mapVals (f : β → γ) (xs : HashMap α β) : HashMap α γ :=
    mkHashMap (capacity := xs.size) |> xs.fold fun acc k v => acc.insert k (f v)

  def fastMapVals (f : α → β → β) (xs : HashMap α β) : HashMap α β :=
    let size := xs.val.size
    let buckets := xs.val.buckets.val.map (·.map f)
    ⟨⟨size, ⟨buckets, sorry⟩⟩, sorry⟩

  def filter (p : α → β → Bool) (xs : HashMap α β) : HashMap α β :=
    let buckets := xs.val.buckets.val.map (·.filter p)
    let size := buckets.foldl (fun acc bucket => bucket.foldl (fun acc _ _ => acc + 1) acc) 0
    ⟨⟨size, ⟨buckets, sorry⟩⟩, sorry⟩

  def getAny? (x : HashMap α β) : Option (α × β) := Id.run <| do
    for bucket in x.val.buckets.val do
      for (k, v) in bucket do
        return some (k, v)
    return none

end Lean.HashMap

structure Equation where
  id     : Nat
  coeffs : HashMap Nat Int
  const  : Int
  deriving Inhabited

def gcd (coeffs : HashMap Nat Int) : Nat :=
  let coeffs := coeffs.mapVals (·.natAbs)
  let coeffsContent := coeffs.toArray
  match coeffsContent with
  | #[]           => panic! "Cannot calculate GCD of empty list of coefficients"
  | #[(i, x)]     => x
  | coeffsContent =>
    coeffsContent[0]!.2.gcd coeffsContent[1]!.2
      |> coeffs.fold fun acc k v => acc.gcd v

namespace Equation

  def preprocess? (e : Equation) : Option Equation := Id.run <| do
    let gcd : Int := gcd e.coeffs
    if e.const % gcd ≠ 0 then
      return none
    return some { e with
      coeffs := e.coeffs.fastMapVals fun _ coeff => coeff / gcd
      const  := e.const / gcd }

  def subst (fromEq toEq : Equation) (varIdx : Nat) : Equation := Id.run <| do
    -- varIdx ≡ k
    -- fromEq ≡ sₖxₖ + ∑ i ∈ V_fromEq\{k}. aᵢxᵢ = A
    --       ⇔ xₖ = sₖA - ∑ i ∈ V_fromEq\{k}. sₖaᵢxᵢ
    -- toEq ≡ bₖxₖ + ∑ i ∈ V_toEq\{k}. bᵢxᵢ = B
    --     ⇝ B = bₖ(sₖA - ∑ i ∈ V_fromEq\{k}. sₖaᵢxᵢ) + ∑ i ∈ V_toEq\{k}. bᵢxᵢ
    --          = bₖsₖA - ∑ i ∈ V_fromEq\{k}. sₖbₖaᵢxᵢ + ∑ i ∈ V_toEq\{k}. bᵢxᵢ
    --          = bₖsₖA + ∑ i ∈ V_fromEq\V_toEq. -sₖbₖaᵢxᵢ
    --                 + ∑ i ∈ V_toEq\{k} ∩ V_fromEq. (bᵢ - sₖbₖaᵢ)xᵢ
    --                 + ∑ i ∈ V_toEq\V_fromEq. bᵢxᵢ
    --     ⇔ B - bₖsₖA = + ∑ i ∈ X. -sₖbₖaᵢxᵢ
    --                   + ∑ i ∈ Y. (bᵢ - sₖbₖaᵢ)xᵢ
    --                   + ∑ i ∈ Z. bᵢxᵢ
    --        with X, Y, Z defined as above, X ∪ Y ∪ Z = (V_fromEq ∪ V_toEq)\{k}
    --        and X, Y, Z pairwise disjoint
    let A := fromEq.const
    let B := toEq.const
    let V_fromEq := fromEq.coeffs
    let V_toEq := toEq.coeffs
    let k := varIdx
    let sₖ := V_fromEq.find! k
    let bₖ := V_toEq.find! k
    let mut V_toEq := V_toEq.fastMapVals fun i bᵢ =>
      match V_fromEq.find? i with
      | none =>
        bᵢ
      | some aᵢ =>
        bᵢ - sₖ*bₖ*aᵢ
    for (i, aᵢ) in V_fromEq do
      if ¬V_toEq.contains i then
        V_toEq := V_toEq.insert i (-sₖ*bₖ*aᵢ)
    V_toEq := V_toEq.filter fun i bᵢ => i ≠ k ∧ bᵢ ≠ 0
    let B' := B - bₖ*sₖ*A
    { toEq with coeffs := V_toEq, const := B' }

  def normalize (e : Equation) : Equation := Id.run <| do
    if e.coeffs.size ≠ 1 then
      return e
    let (i, c) := e.coeffs.getAny?.get!
    return { e with
      coeffs := e.coeffs.insert i 1
      const := Int.div e.const c }

  def invert (e : Equation) : Equation :=
    { e with
      coeffs := e.coeffs.fastMapVals fun _ coeff => (-1)*coeff
      const  := (-1)*e.const }

  def reorganizeFor (e : Equation) (varIdx : Nat) : Equation := Id.run <| do
    let singletonCoeff := e.coeffs.find! varIdx
    let mut e := { e with coeffs := e.coeffs.fastMapVals fun _ coeff => (-1)*coeff }
    if singletonCoeff = -1 then
      e := e.invert
    { e with coeffs := e.coeffs.erase varIdx }

  def findSingleton? (e : Equation) : Option (Nat × Int) := Id.run <| do
    for (i, coeff) in e.coeffs do
      if coeff = 1 ∨ coeff = -1 then
        return some (i, coeff)
    return none

  def findAbsMinimumCoeff? (e : Equation) : Option (Nat × Int) := Id.run <| do
    let mut r? : Option (Nat × Int) := none
    for (i, coeff) in e.coeffs do
      match r? with
      | none =>
        r? := some (i, coeff)
      | some (i', coeff') =>
        if coeff.natAbs < coeff'.natAbs then
          r? := some (i, coeff)
    return r?

end Equation

structure Problem where
  equations       : HashMap Nat Equation
  solvedEquations : HashMap Nat Equation
  nEquations      : Nat
  nVars           : Nat
  deriving Inhabited

def preprocess? (eqs : HashMap Nat Equation) : Option (HashMap Nat Equation) :=
  eqs.mapValsM (·.preprocess?)

def eliminateSingleton (p : Problem) (singletonEq : Equation) (varIdx : Nat) : Problem := Id.run <| do
  let mut eqsWithVarIdx : Array Nat := #[]
  for (id, eq) in p.equations do
    if eq.coeffs.contains varIdx then
      eqsWithVarIdx := eqsWithVarIdx.push id
  let mut equations := p.equations
  for id in eqsWithVarIdx do
    if id == singletonEq.id then
      continue
    equations := equations.modify! id fun eq => singletonEq.subst eq varIdx |>.normalize
  equations := equations.erase singletonEq.id
  let solvedEquations := p.solvedEquations.insert varIdx <| singletonEq.reorganizeFor varIdx
  return { p with
    equations := equations
    solvedEquations := solvedEquations }

partial def eliminateSingletons (p : Problem) : Problem := Id.run <| do
  let mut r? : Option (Equation × Nat) := none
  for (id, eq) in p.equations do
    match eq.findSingleton? with
    | none =>
      continue
    | some (varIdx, coeff) =>
      r? := some (eq, varIdx)
  match r? with
  | none =>
    return p
  | some (eq, varIdx) =>
    let p := eliminateSingleton p eq varIdx
    return eliminateSingletons p

def addAuxEquation (p : Problem) : Problem := Id.run <| do
  let mut E? : Option Equation := none
  let mut k? : Option Nat := none
  let mut aₖ? : Option Int := none
  for (_, eq) in p.equations do
    match eq.findAbsMinimumCoeff?, aₖ? with
    | none, _ => continue
    | some (k', aₖ'), none =>
      E? := some eq
      k? := some k'
      aₖ? := some aₖ'
    | some (k', aₖ'), some aₖ =>
      if aₖ'.natAbs < aₖ.natAbs then
        E? := some eq
        k? := some k'
        aₖ? := some aₖ'
  let mut E := E?.get!
  let k := k?.get!
  let mut aₖ := aₖ?.get!
  if aₖ < 0 then
    aₖ := -aₖ
    E := E.invert
  let m := aₖ + 1
  let σIdx := p.nVars
  let newEqCoeffs := E.coeffs.fastMapVals (fun _ coeff => coeff.mod' m)
    |>.insert σIdx (-m)
    |>.filter (fun _ coeff => coeff ≠ 0)
  let newEqConst := E.const.mod' m
  let newEq : Equation := ⟨p.nEquations, newEqCoeffs, newEqConst⟩
  let E'coeffs := E.coeffs.filter (fun i _ => i ≠ k)
    |>.fastMapVals (fun _ aᵢ => aᵢ.roundedDiv m + aᵢ.mod' m)
    |>.insert σIdx (-aₖ)
    |>.filter (fun _ coeff => coeff ≠ 0)
  let c := E.const
  let E'const := c.roundedDiv m + c.mod' m
  let E' := { E with coeffs := E'coeffs, const := E'const }.normalize
  let equations' := p.equations.insert E'.id E' |>.insert newEq.id newEq
  let p' : Problem := { p with
                        equations  := equations'
                        nVars      := p.nVars + 1
                        nEquations := p.nEquations + 1 }
  return eliminateSingleton p' newEq k

inductive Solution
  | unsat
  | sat (assignment : Array Int)
  deriving Inhabited

partial def readSolution? (p : Problem) : Option Solution := Id.run <| do
  if p.equations.any (fun _ eq => eq.coeffs.size ≠ 0) then
    return none
  if p.equations.any (fun _ eq => eq.const ≠ 0) then
    return some Solution.unsat
  let mut assignment : Array (Option Int) := mkArray p.nVars none
  for i in [0:p.nVars] do
    assignment := readSolution i assignment
  return Solution.sat <| assignment.map (·.get!)
where
  readSolution (varIdx : Nat) (assignment : Array (Option Int)) : Array (Option Int) := Id.run <| do
    match p.solvedEquations.find? varIdx with
    | none =>
      return assignment.set! varIdx (some 0)
    | some eq =>
      let mut assignment := assignment
      let mut r := eq.const
      for (i, coeff) in eq.coeffs do
        if assignment[i]!.isNone then
          assignment := readSolution i assignment
        r := r + coeff*assignment[i]!.get!
      return assignment.set! varIdx (some r)

partial def solveProblem' (p : Problem) : Solution := Id.run <| do
  match readSolution? p with
  | some solution => return solution
  | none =>
    let p := eliminateSingletons p
    match readSolution? p with
    | some solution => return solution
    | none =>
      let p := addAuxEquation p
      return solveProblem' p

def isSatAssignment (p : Problem) (assignment : Array Int) : Bool :=
  ¬ p.equations.any fun _ (eq : Equation) => Id.run <| do
    let mut r := 0
    for (i, coeff) in eq.coeffs do
      r := r + coeff*assignment[i]!
    return r ≠ eq.const

def solveProblem (p : Problem) : Solution :=
  let nVars := p.nVars
  match solveProblem' p with
  | Solution.unsat =>
    Solution.unsat
  | Solution.sat assignment =>
    let assignment' := assignment.extract 0 nVars
    if isSatAssignment p assignment' then
      Solution.sat assignment'
    else
      Solution.unsat

def error (msg : String) : IO α :=
  throw <| IO.userError s!"Error: {msg}."

def Array.ithVal (xs : Array String) (i : Nat) (name : String) : IO Int := do
  let some unparsed := xs.get? i
    | error s!"Missing {name}"
  let some parsed := String.toInt? unparsed
    | error s!"Invalid {name}: `{unparsed}`"
  return parsed

def main (args : List String) : IO UInt32 := do
  let some path := args.head?
    | error "Usage: liasolver <input file>"
  let lines ← IO.FS.lines path <&> Array.filter (¬·.isEmpty)
  let some headerLine := lines.get? 0
    | error "No header line"
  let header := headerLine.splitOn.toArray
  let nEquations ← header.ithVal 0 "amount of equations"
  let nVars ← header.ithVal 1 "amount of variables"
  let mut equations : HashMap Nat Equation := mkHashMap
  for line in lines[1:] do
    let elems := line.splitOn.toArray
    let nTerms ← elems.ithVal 0 "amount of equation terms"
    let 0 ← elems.ithVal (elems.size - 1) "end of line symbol"
      | error "Non-zero end of line symbol"
    let const ← elems.ithVal (elems.size - 2) "constant value"
    let mut coeffs := mkHashMap
    for i in [1:elems.size-2:2] do
      let coeff ← elems.ithVal i "coefficient"
      let varIdx ← elems.ithVal (i + 1) "variable index"
      if varIdx < 1 then
        error "Invalid variable index"
      let varIdx := varIdx.toNat - 1
      if coeff ≠ 0 then
        coeffs := coeffs.insert varIdx coeff
    if coeffs.size ≠ 0 then
      equations := equations.insert equations.size ⟨equations.size, coeffs, const⟩
  match preprocess? equations with
  | none =>
    IO.println "UNSAT"
  | some equations' =>
    let problem : Problem := ⟨equations', mkHashMap, equations'.size, nVars.natAbs⟩
    match solveProblem problem with
    | Solution.unsat =>
      IO.println "UNSAT"
    | Solution.sat assignment =>
      IO.println "SAT"
      IO.println <| String.intercalate " " <| assignment.toList.map toString
  return 0
