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
import Lean.Meta.Sym.Eta
import Lean.Meta.LetToHave
namespace Lean.Meta.Sym

/--
Zeta-reduces `type`, except for the `have`s and nondependent `let`s in the domains of its first
`num?` binders (all if `none`), which become `have`s. A backward rule turns these domains into new
goals.
-/
partial def zetaReduceExceptDomainHaves (type : Expr) (num? : Option Nat) (zetaDelta : Bool) : MetaM Expr :=
  go type num? #[] #[]
where
  -- `subst` instantiates the loose bound variables of `type`; `xs` are the binders among them.
  go (type : Expr) (num? : Option Nat) (subst xs : Array Expr) : MetaM Expr := do
    if num? != some 0 then
      match type with
      | .forallE n d b bi =>
        let d ← letToHave (d.instantiateRev subst)
        let d ← zetaReduce d (zetaDelta := zetaDelta) (zetaHave := false)
        return ← withLocalDecl n bi d fun x => go b (num?.map (· - 1)) (subst.push x) (xs.push x)
      | .letE _ _ v b _ => return ← go b num? (subst.push (v.instantiateRev subst)) xs
      | _ => pure ()
    mkForallFVars xs (← zetaReduce (type.instantiateRev subst) (zetaDelta := zetaDelta))

/--
Preprocesses types that used for pattern matching and unification.
`num?` is the number of binders that become pattern variables (all if `none`).
-/
public def preprocessType (type : Expr) (zetaReduceLHSOnly := false) (zetaDelta := false)
    (num? : Option Nat := none) : MetaM Expr := do
  let type ← Sym.unfoldReducible type
  let type ← Core.betaReduce type
  let type ← if zetaReduceLHSOnly then
    forallTelescope type fun xs body => do
      match_expr body with
      | f@Eq α lhs rhs => mkForallFVars xs <| mkApp3 f α (← zetaReduce lhs (zetaDelta := zetaDelta)) rhs
      | f@Iff lhs rhs => mkForallFVars xs <| mkApp2 f (← zetaReduce lhs (zetaDelta := zetaDelta)) rhs
      | _ => zetaReduce type (zetaDelta := zetaDelta)
  else
    zetaReduceExceptDomainHaves type num? zetaDelta
  etaReduceAll type

/--
Analyzes whether the given free variables (aka arguments) are proofs or instances.
Returns `none` if no arguments are proofs or instances.
-/
public def mkProofInstArgInfo? (xs : Array Expr) : MetaM (Option ProofInstInfo) := do
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
Analyzes the type signature of `declName` and returns information about which arguments
are proofs or instances. Returns `none` if no arguments are proofs or instances.
-/
public def mkProofInstInfo? (declName : Name) : MetaM (Option ProofInstInfo) := do
  let info ← getConstInfo declName
  let type ← preprocessType info.type
  forallTelescopeReducing type fun xs _ => mkProofInstArgInfo? xs

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

/--
Returns information about the type of the local declaration `fvarId`. It contains information about
which arguments are proofs or instances. Returns `none` if no arguments are proofs or instances.
-/
public def getProofInstInfoOfFVar? (fvarId : FVarId) : SymM (Option ProofInstInfo) := do
  if let some r := (← get).proofInstInfoFVar.find? fvarId then
    return r
  else
    let r ← forallTelescopeReducing (← fvarId.getType) fun xs _ => mkProofInstArgInfo? xs
    modify fun s => { s with proofInstInfoFVar := s.proofInstInfoFVar.insert fvarId r }
    return r

/--
Returns information about which arguments of the function `e` are proofs or instances, see
`getProofInstInfo?` and `getProofInstInfoOfFVar?`. Returns `none` if `e` is neither a constant
nor a local declaration.
-/
public def getProofInstInfoOfExpr? (e : Expr) : SymM (Option ProofInstInfo) := do
  match e with
  | .const declName _ => getProofInstInfo? declName
  | .fvar fvarId => getProofInstInfoOfFVar? fvarId
  | _ => return none -- TODO: if needed

end Lean.Meta.Sym
