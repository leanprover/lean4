/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.IsClass
import Lean.Meta.Sym.Util
import Lean.Meta.Transform
namespace Lean.Meta.Sym

/--
Preprocesses types that used for pattern matching and unification.
-/
public def preprocessType (type : Expr) : MetaM Expr := do
  let type ← Sym.unfoldReducible type
  let type ← Core.betaReduce type
  zetaReduce type

/--
Analyzes the type signature of `declName` and returns information about which arguments
are proofs or instances. Returns `none` if no arguments are proofs or instances.
-/
public def mkProofInstInfo? (declName : Name) : MetaM (Option ProofInstInfo) := do
  let info ← getConstInfo declName
  let type ← preprocessType info.type
  forallTelescopeReducing type fun xs _ => do
    let env ← getEnv
    let mut argsInfo := #[]
    let mut found := false
    for x in xs do
      let type ← Meta.inferType x
      let isInstance := isClass? env type |>.isSome
      let isProof ← isProp type
      if isInstance || isProof then
        found := true
      argsInfo := argsInfo.push { isInstance, isProof }
    if found then
      return some { argsInfo }
    else
      return none

/--
Returns information about the type signature of `declName`. It contains information about which arguments
are proofs or instances. Returns `none` if no arguments are proofs or instances.
-/
public def getProofInstInfo? (declName : Name) : SymM (Option ProofInstInfo) := do
  if let some r := (← get).proofInstInfo.find? declName then
    return r
  else
    let r ← mkProofInstInfo? declName
    modify fun s => { s with proofInstInfo := s.proofInstInfo.insert declName r }
    return r

end Lean.Meta.Sym
