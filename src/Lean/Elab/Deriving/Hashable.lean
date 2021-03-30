/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Hashable
open Command
open Lean.Parser.Term
open Meta

/--
  Computes at least the first `n` primes. Usually slightly more
-/
private def firstNPrimes (n : Nat) : Array Nat := do
  if n ≥ 6 then
    let n := Float.ofInt n
    -- for n ≥ 6, n log n + n log log n is an upper bound for the n-th prime
    let upperBound := n * (Float.log n + (Float.log $ Float.log n))
    let nRoot := Float.sqrt upperBound |> Float.toUInt32 |> UInt32.toNat
    let upperBound := upperBound |> Float.toUInt32 |> UInt32.toNat
    let mut primes := #[false, false] ++ mkArray (upperBound - 1) true
    for p in [2:nRoot] do
      if primes[p] then
        for i in [p*p:upperBound+1:p] do 
          primes := primes.set! i false
    return primes.mapIdx (λ i v => if v then some i.1 else none) |> Array.filterMap id
  else
    return #[2,3,5,7,11,13]

def mkHashableHeader (ctx : Context) (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ctx `Hashable 1 indVal

def mkMatch (offset : Nat) (primes : Array Nat) (ctx : Context) (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Syntax := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where

  mkAlts : TermElabM (Array Syntax) := do
    let mut alts := #[]
    let mut ctorIdx := 0
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
        let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
        let mut patterns := #[]
        -- add `_` pattern for indices
        for i in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhs ← `($(quote primes[offset + ctorIdx]))
        -- add `_` for inductive parameters, they are inaccessible
        for i in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]
          let xTy ← inferType x
          let typeName := xTy.getAppFn.constName!
          if indVal.all.contains typeName then
            -- If the value depends of any of the mutually recursive types, ignore it → add `_`. 
            -- We want hash computation to be O(1).
            ctorArgs := ctorArgs.push (← `(_))
          else
            let a := mkIdent (← mkFreshUserName `a)
            ctorArgs := ctorArgs.push a
            rhs ← `(mixHash $rhs (hash $a:ident))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
      ctorIdx := ctorIdx + 1
    return alts

def mkAuxFunction (offset : Nat) (primes : Array Nat) (ctx : Context) (i : Nat) : TermElabM Syntax := do
  let auxFunName ← ctx.auxFunNames[i]
  let indVal     ← ctx.typeInfos[i]
  let header     ← mkHashableHeader ctx indVal
  let body       ← mkMatch offset primes ctx header indVal auxFunName
  let binders    := header.binders
  `(private def $(mkIdent auxFunName):ident $binders:explicitBinder* : USize := $body:term) 

def mkHashFuncs (ctx : Context) : TermElabM (Array Syntax) := do
  let nCtors := ctx.typeInfos.map (·.ctors.length) 
  let primes := nCtors.foldl (· + ·) 0 |> firstNPrimes
  let mut auxDefs := #[]
  let mut offset := 0
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction offset primes ctx i)
    offset := nCtors[i]
  auxDefs

private def mkHashableInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "hash" declNames[0]
  let cmds := (← mkHashFuncs ctx) ++ (← mkInstanceCmds ctx `Hashable declNames)
  trace[Elab.Deriving.hashable] "\n{cmds}"
  return cmds

def mkHashableHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM none <| mkHashableInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerBuiltinDerivingHandler ``Hashable mkHashableHandler
  registerTraceClass `Elab.Deriving.hashable