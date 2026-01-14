/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
public import Lean.Meta.Tactic.Grind.Arith.Util
import Init.Grind.Module.OfNatModule
import Lean.Data.RArray
import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Grind.Arith.CommRing.VarRename
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
public section
namespace Lean.Meta.Grind.Arith.Linear

open CommRing (RingExpr)

/--
Returns a context of type `RArray α` containing the variables of the given structure, where
`α` is `(← getStruct).type`.
-/
def toContextExpr (vars : Array Expr) : LinearM Expr := do
  let struct ← getStruct
  if h : 0 < vars.size then
    RArray.toExpr struct.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr struct.type id (RArray.leaf struct.zero)

structure ProofM.State where
  cache         : Std.HashMap UInt64 Expr := {}
  varDecls      : Std.HashMap Var Expr := {}
  polyDecls     : Std.HashMap Poly Expr := {}
  exprDecls     : Std.HashMap LinExpr Expr := {}
  ringPolyDecls : Std.HashMap CommRing.Poly Expr := {}
  ringExprDecls : Std.HashMap RingExpr Expr := {}
  ringVarDecls  : Std.HashMap Var Expr := {}

structure ProofM.Context where
  ctx     : Expr
  ringCtx : Expr

/-- Auxiliary monad for constructing linarith proofs. -/
abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State LinearM)

/-- Returns a Lean expression representing the variable context used to construct linarith proofs. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

/--
Returns a Lean expression representing the auxiliary `CommRing` variable context
used to construct linarith proofs.
-/
private abbrev getRingContext : ProofM Expr := do
  return (← read).ringCtx

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

local macro "declare! " decls:ident a:ident : term =>
  `(do if let some x := (← get).$decls[$a]? then
         return x
       let x := mkFVar (← mkFreshFVarId);
       modify fun s => { s with $decls:ident := (s.$decls).insert $a x };
       return x)

def mkVarDecl (x : Var) : ProofM Expr := do
  declare! varDecls x

def mkPolyDecl (p : Poly) : ProofM Expr := do
  declare! polyDecls p

def mkExprDecl (e : LinExpr) : ProofM Expr := do
  declare! exprDecls e

def mkRingPolyDecl (p : CommRing.Poly) : ProofM Expr := do
  declare! ringPolyDecls p

def mkRingExprDecl (e : RingExpr) : ProofM Expr := do
  declare! ringExprDecls e

def mkRingVarDecl (x : Var) : ProofM Expr := do
  declare! ringVarDecls x

private def mkContext (h : Expr) : ProofM Expr := do
  let varDecls     := (← get).varDecls
  let polyDecls    := (← get).polyDecls
  let exprDecls    := (← get).exprDecls
  let usedVars     :=
    collectMapVars varDecls collectVar >>
    collectMapVars polyDecls (·.collectVars) >>
    collectMapVars exprDecls (·.collectVars) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getStruct).vars
  let vars         := vars'.map fun x => vars[x]!
  let varFVars     := vars'.map fun x => varDecls[x]?.getD default
  let varIdsAsExpr := List.range vars'.size |>.toArray |>.map toExpr
  let h := h.replaceFVars varFVars varIdsAsExpr
  let h := mkLetOfMap exprDecls h `e (mkConst ``Grind.Linarith.Expr) fun e => toExpr <| e.renameVars varRename
  let h := mkLetOfMap polyDecls h `p (mkConst ``Grind.Linarith.Poly) fun p => toExpr <| p.renameVars varRename
  let h := h.abstract #[(← read).ctx]
  if h.hasLooseBVars then
    let struct ← getStruct
    let ctxType := mkApp (mkConst ``RArray [struct.u]) struct.type
    let ctxVal ← toContextExpr vars
    return .letE `ctx ctxType ctxVal h (nondep := false)
  else
    return h

private def mkRingContext (h : Expr) : ProofM Expr := do
  unless (← isCommRing) do return h
  let ring ← withRingM do CommRing.getRing
  let vars := ring.vars
  let ringVarDecls := (← get).ringVarDecls
  let usedVars     := collectMapVars (← get).ringPolyDecls (·.collectVars) >> collectMapVars (← get).ringExprDecls (·.collectVars) >> collectMapVars ringVarDecls collectVar <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => vars[x]!
  let h := mkLetOfMap (← get).ringExprDecls h `re (mkConst ``Grind.CommRing.Expr) fun e => toExpr <| e.renameVars varRename
  let h := mkLetOfMap (← get).ringPolyDecls h `rp (mkConst ``Grind.CommRing.Poly) fun p => toExpr <| p.renameVars varRename
  -- Replace ring variable FVars with their renamed indices
  let varFVars     := ringVarDecls.toArray.map (·.2)
  let varIdsAsExpr := ringVarDecls.toArray.map fun (v, _) => toExpr (varRename v)
  let h := h.replaceFVars varFVars varIdsAsExpr
  let h := h.abstract #[(← read).ringCtx]
  if h.hasLooseBVars then
    let struct ← getStruct
    let ctxType := mkApp (mkConst ``RArray [struct.u]) struct.type
    let ctxVal ← toContextExpr vars
    return .letE `rctx ctxType ctxVal h (nondep := false)
  else
    return h

private abbrev withProofContext (x : ProofM Expr) : LinearM Expr := do
  let ctx := mkFVar (← mkFreshFVarId)
  let ringCtx := mkFVar (← mkFreshFVarId)
  go { ctx, ringCtx } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkRingContext h
    mkContext h

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [IntModule α] (ctx : Context α)`
-/
private def mkIntModThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.intModuleInst (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α)`
-/
private def mkIntModNoNatDivThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type s.intModuleInst (← getNoNatDivInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first four arguments are
`{α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α)`
-/
private def mkIntModPreThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp7 (mkConst declName [s.u]) s.type s.intModuleInst (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsPreorderInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] (ctx : Context α)`
This is one of the most common theorem prefixes at `Linarith.lean`
-/
private def mkIntModPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp6 (mkConst declName [s.u]) s.type s.intModuleInst (← getLEInst) (← getIsPreorderInst) (← getOrderedAddInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] (ctx : Context α)`
This is one of the most common theorem prefixes at `Linarith.lean`
-/
private def mkIntModLawfulPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp8 (mkConst declName [s.u]) s.type s.intModuleInst (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsPreorderInst) (← getOrderedAddInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (ctx : Context α)`
This is the most common theorem prefix at `Linarith.lean`
-/
private def mkIntModLinOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp8 (mkConst declName [s.u]) s.type s.intModuleInst (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsLinearOrderInst) (← getOrderedAddInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [CommRing α] (rctx : Context α)`
-/
private def mkCommRingThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first four arguments are
`{α} [CommRing α] [NoNatZeroDivisors α] (rctx : Context α)`
-/
private def mkCommRingNoNatDivThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getNoNatDivInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first four arguments are
`{α} [CommRing α] [LE α] (rctx : Context α)`
-/
private def mkCommRingLEThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLEInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first four arguments are
`{α} [CommRing α] [LT α] (rctx : Context α)`
-/
private def mkCommRingLTThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLTInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (rctx : Context α)`
-/
private def mkCommRingPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp7 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLEInst) (← getLTInst) (← getIsPreorderInst) (← getOrderedRingInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (rctx : Context α)`
-/
private def mkCommRingLawfulPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp8 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsPreorderInst) (← getOrderedRingInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (rctx : Context α)`
-/
private def mkCommRingLinOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp8 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsLinearOrderInst) (← getOrderedRingInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [Field α] [IsCharP α 0]`
-/
private def mkFieldChar0ThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.fieldInst?.get! s.charInst?.get!.1

partial def RingIneqCnstr.toExprProof (c' : RingIneqCnstr) : ProofM Expr := do
  match c'.h with
  | .core e lhs rhs =>
    let h' ← if c'.strict then mkCommRingLawfulPreOrdThmPrefix ``Grind.CommRing.lt_norm else mkCommRingPreOrdThmPrefix ``Grind.CommRing.le_norm
    return mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl c'.p) eagerReflBoolTrue (mkOfEqTrueCore e (← mkEqTrueProof e))
  | .notCore e lhs rhs =>
    let h' ← mkCommRingLinOrdThmPrefix (if c'.strict then ``Grind.CommRing.not_le_norm else ``Grind.CommRing.not_lt_norm)
    return mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl c'.p) eagerReflBoolTrue (mkOfEqFalseCore e (← mkEqFalseProof e))
  | .cancelDen c val x n =>
    let h ← if c.strict then
      mkCommRingLawfulPreOrdThmPrefix ``Grind.CommRing.lt_mul
    else
      mkCommRingPreOrdThmPrefix ``Grind.CommRing.le_mul
    let p₁ := c.p.mulConst (val^n)
    let p₁ ← mkRingPolyDecl p₁
    let h := mkApp5 h (← mkRingPolyDecl c.p) (toExpr (val^n)) p₁ eagerReflBoolTrue (← c.toExprProof)
    let h_eq_one := mkApp2 (← mkFieldChar0ThmPrefix ``Grind.CommRing.inv_int_eq') (toExpr val) eagerReflBoolTrue
    let h' ← if c.strict then
      mkCommRingLTThmPrefix ``Grind.CommRing.lt_cancel_var
    else
      mkCommRingLEThmPrefix ``Grind.CommRing.le_cancel_var
    return mkApp7 h' (toExpr val) (← mkRingVarDecl x) p₁ (← mkRingPolyDecl c'.p) eagerReflBoolTrue h_eq_one h

partial def RingEqCnstr.toExprProof (c' : RingEqCnstr) : ProofM Expr := do
  match c'.h with
  | .core a b la lb =>
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.eq_norm
    return mkApp5 h' (← mkRingExprDecl la) (← mkRingExprDecl lb) (← mkRingPolyDecl c'.p) eagerReflBoolTrue (← mkEqProof a b)
  | .symm c =>
    let h ← c.toExprProof
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.Stepwise.inv
    return mkApp4 h' (← mkRingPolyDecl c.p) (← mkRingPolyDecl c'.p) eagerReflBoolTrue h
  | .cancelDen c val x n =>
    let h ← mkCommRingThmPrefix ``Grind.CommRing.Stepwise.eq_mul
    let p₁ := c.p.mulConst (val^n)
    let p₁ ← mkRingPolyDecl p₁
    let h := mkApp5 h (← mkRingPolyDecl c.p) (toExpr (val^n)) p₁ eagerReflBoolTrue (← c.toExprProof)
    let h_eq_one := mkApp2 (← mkFieldChar0ThmPrefix ``Grind.CommRing.inv_int_eq') (toExpr val) eagerReflBoolTrue
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.eq_cancel_var
    return mkApp7 h' (toExpr val) (← mkRingVarDecl x) p₁ (← mkRingPolyDecl c'.p) eagerReflBoolTrue h_eq_one h

partial def RingDiseqCnstr.toExprProof (c' : RingDiseqCnstr) : ProofM Expr := do
  match c'.h with
  | .core a b lhs rhs =>
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.diseq_norm
    return mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl c'.p) eagerReflBoolTrue (← mkDiseqProof a b)
  | .cancelDen c val x n =>
    let h ← mkCommRingNoNatDivThmPrefix ``Grind.CommRing.Stepwise.diseq_mul
    let p₁ := c.p.mulConst (val^n)
    let p₁ ← mkRingPolyDecl p₁
    let h := mkApp5 h (← mkRingPolyDecl c.p) (toExpr (val^n)) p₁ eagerReflBoolTrue (← c.toExprProof)
    let h_eq_one := mkApp2 (← mkFieldChar0ThmPrefix ``Grind.CommRing.inv_int_eq') (toExpr val) eagerReflBoolTrue
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.diseq_cancel_var
    return mkApp7 h' (toExpr val) (← mkRingVarDecl x) p₁ (← mkRingPolyDecl c'.p) eagerReflBoolTrue h_eq_one h

mutual
partial def IneqCnstr.toExprProof (c' : IneqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core e lhs rhs =>
    let h ← if c'.strict then mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.lt_norm else mkIntModPreOrdThmPrefix ``Grind.Linarith.le_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue (mkOfEqTrueCore e (← mkEqTrueProof e))
  | .notCore e lhs rhs =>
    let h ← mkIntModLinOrdThmPrefix (if c'.strict then ``Grind.Linarith.not_le_norm else ``Grind.Linarith.not_lt_norm)
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue (mkOfEqFalseCore e (← mkEqFalseProof e))
  | .ring c lhs' =>
    let h ← c.toExprProof
    let h' ← if c'.strict then mkCommRingLTThmPrefix ``Grind.CommRing.lt_int_module else mkCommRingLEThmPrefix ``Grind.CommRing.le_int_module
    let h' := mkApp2 h' (← mkRingPolyDecl c.p) h
    let h ← if c'.strict then mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.lt_norm else mkIntModPreOrdThmPrefix ``Grind.Linarith.le_norm
    return mkApp5 h (← mkExprDecl lhs') (← mkExprDecl .zero) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .coreOfNat e natStructId lhs rhs =>
    let h' ← OfNatModuleM.run natStructId do
      let a := e.appFn!.appArg!
      let b := e.appArg!
      let ns ← getNatStruct
      let (a', ha) ← ofNatModule a
      let (b', hb) ← ofNatModule b
      let h := if c'.strict then
        mkApp7 (mkConst ``Grind.IntModule.OfNatModule.of_lt [ns.u]) ns.type ns.natModuleInst ns.leInst?.get! ns.ltInst?.get!
          ns.lawfulOrderLTInst?.get! ns.isPreorderInst?.get! ns.orderedAddInst?.get!
      else
        mkApp5 (mkConst ``Grind.IntModule.OfNatModule.of_le [ns.u]) ns.type ns.natModuleInst ns.leInst?.get!
          ns.isPreorderInst?.get! ns.orderedAddInst?.get!
      return mkApp7 h a b a' b' ha hb (mkOfEqTrueCore e (← mkEqTrueProof e))
    let h ← if c'.strict then mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.lt_norm else mkIntModPreOrdThmPrefix ``Grind.Linarith.le_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .notCoreOfNat e natStructId lhs rhs =>
    let h' ← OfNatModuleM.run natStructId do
      let a := e.appFn!.appArg!
      let b := e.appArg!
      let ns ← getNatStruct
      let (a', ha) ← ofNatModule a
      let (b', hb) ← ofNatModule b
      let h := if c'.strict then
        mkApp5 (mkConst ``Grind.IntModule.OfNatModule.of_not_le [ns.u]) ns.type ns.natModuleInst ns.leInst?.get!
          ns.isPreorderInst?.get! ns.orderedAddInst?.get!
      else
        mkApp7 (mkConst ``Grind.IntModule.OfNatModule.of_not_lt [ns.u]) ns.type ns.natModuleInst ns.leInst?.get! ns.ltInst?.get!
          ns.lawfulOrderLTInst?.get! ns.isPreorderInst?.get! ns.orderedAddInst?.get!
      return mkApp7 h a b a' b' ha hb (mkOfEqFalseCore e (← mkEqFalseProof e))
    let h ← mkIntModLinOrdThmPrefix (if c'.strict then ``Grind.Linarith.not_le_norm else ``Grind.Linarith.not_lt_norm)
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .combine c₁ c₂ =>
    let (pre, c₁, c₂) :=
      match c₁.strict, c₂.strict with
      | true, true => (mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.lt_lt_combine, c₁, c₂)
      | true, false => (mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.le_lt_combine, c₂, c₁)
      | false, true => (mkIntModLawfulPreOrdThmPrefix ``Grind.Linarith.le_lt_combine, c₁, c₂)
      | false, false => (mkIntModPreOrdThmPrefix ``Grind.Linarith.le_le_combine, c₁, c₂)
    return mkApp6 (← pre) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) eagerReflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .oneGtZero =>
    let s ← getStruct
    let h := mkApp8 (mkConst ``Grind.Linarith.zero_lt_one [s.u]) s.type (← getRingInst) (← getLEInst) (← getLTInst) (← getLawfulOrderLTInst) (← getIsPreorderInst) (← getOrderedRingInst) (← getContext)
    return mkApp3 h (← mkPolyDecl c'.p) eagerReflBoolTrue (← mkEqRefl (← getOne))
  | .ofEq a b la lb =>
    let h ← mkIntModPreOrdThmPrefix ``Grind.Linarith.le_of_eq
    return mkApp5 h (← mkExprDecl la) (← mkExprDecl lb) (← mkPolyDecl c'.p) eagerReflBoolTrue (← mkEqProof a b)
  | .ofEqOfNat a b natStructId la lb =>
    let h' ← OfNatModuleM.run natStructId do
      let ns ← getNatStruct
      let (a', ha) ← ofNatModule a
      let (b', hb) ← ofNatModule b
      return mkApp9 (mkConst ``Grind.IntModule.OfNatModule.of_eq [ns.u]) ns.type ns.natModuleInst
        a b a' b' ha hb (← mkEqProof a b)
    let h ← mkIntModPreOrdThmPrefix ``Grind.Linarith.le_of_eq
    return mkApp5 h (← mkExprDecl la) (← mkExprDecl lb) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .ringEq c lhs =>
    let h' ← c.toExprProof
    let h' := mkApp2 (← mkCommRingThmPrefix ``Grind.CommRing.eq_int_module) (← mkRingPolyDecl c.p) h'
    let h ← mkIntModPreOrdThmPrefix ``Grind.Linarith.le_of_eq
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl .zero) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .dec h => return mkFVar h
  | .ofDiseqSplit c₁ fvarId h _ =>
    let hFalse ← h.toExprProofCore
    let lt ← getLtFn
    let hNot := mkLambda `h .default (mkApp2 lt (← c₁.p.denoteExpr) (← getZero)) (hFalse.abstract #[mkFVar fvarId])
    let h ← mkIntModLinOrdThmPrefix ``Grind.Linarith.diseq_split_resolve
    return mkApp5 h (← mkPolyDecl c₁.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c₁.toExprProof) hNot
  | .subst .. | .norm .. =>  throwError "NIY"

partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core a b lhs rhs =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue (← mkDiseqProof a b)
  | .ring c lhs =>
    let h' ← c.toExprProof
    let h' := mkApp2 (← mkCommRingThmPrefix ``Grind.CommRing.diseq_int_module) (← mkRingPolyDecl c.p) h'
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl .zero) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .coreOfNat a b natStructId lhs rhs =>
    let h ← OfNatModuleM.run natStructId do
      let ns ← getNatStruct
      let (a', ha) ← ofNatModule a
      let (b', hb) ← ofNatModule b
      return mkApp10 (mkConst ``Grind.IntModule.OfNatModule.of_diseq [ns.u]) ns.type ns.natModuleInst ns.addRightCancelInst?.get!
        a b a' b' ha hb (← mkDiseqProof a b)
    return mkApp5 (← mkIntModThmPrefix ``Grind.Linarith.diseq_norm)
      (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .neg c =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_neg
    return mkApp4 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .subst k₁ k₂ c₁ c₂ =>
    let h ← mkIntModNoNatDivThmPrefix ``Grind.Linarith.eq_diseq_subst
    return mkApp8 h (toExpr k₁) (toExpr k₂) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst1 k c₁ c₂ =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_diseq_subst1
    return mkApp7 h (toExpr k) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) eagerReflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .oneNeZero => throwError "not implemented yet"

partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core a b lhs rhs =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue (← mkEqProof a b)
  | .coreCommRing .. => throwError "not implemented yet"
  | .coreOfNat a b natStructId lhs rhs =>
    let h' ← OfNatModuleM.run natStructId do
      let ns ← getNatStruct
      let (a', ha) ← ofNatModule a
      let (b', hb) ← ofNatModule b
      return mkApp9 (mkConst ``Grind.IntModule.OfNatModule.of_eq [ns.u]) ns.type ns.natModuleInst
        a b a' b' ha hb (← mkEqProof a b)
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h'
  | .neg c =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_neg
    return mkApp4 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .coeff k c =>
    let h ← mkIntModNoNatDivThmPrefix ``Grind.Linarith.eq_coeff
    return mkApp5 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂ =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_eq_subst
    return mkApp7 h (← mkVarDecl x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) eagerReflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)

partial def UnsatProof.toExprProofCore (h : UnsatProof) : ProofM Expr := do
  match h with
  | .lt c => return mkApp (← mkIntModPreThmPrefix ``Grind.Linarith.lt_unsat) (← c.toExprProof)
  | .diseq c => return mkApp (← mkIntModThmPrefix ``Grind.Linarith.diseq_unsat) (← c.toExprProof)

end

def UnsatProof.toExprProof (h : UnsatProof) : LinearM Expr := do
  withProofContext do h.toExprProofCore

def setInconsistent (h : UnsatProof) : LinearM Unit := do
  if (← getStruct).caseSplits then
    -- Let the search procedure in `SearchM` resolve the conflict.
    modifyStruct fun s => { s with conflict? := some h }
  else
    let h ← h.toExprProof
    closeGoal h

def propagateImpEq (c : EqCnstr) : LinearM Unit := do
  let .add 1 x (.add (-1) y .nil) := c.p | unreachable!
  let a ← getVar x
  let b ← getVar y
  let h ← withProofContext do
    let h ← mkIntModThmPrefix ``Grind.Linarith.imp_eq
    return mkApp5 h (← mkPolyDecl c.p) (← mkVarDecl x) (← mkVarDecl y) eagerReflBoolTrue (← c.toExprProof)
  let h := mkExpectedPropHint h (← mkEq a b)
  pushEq a b h

/-!
A linarith proof may depend on decision variables.
We collect them and perform non chronological backtracking.
-/
open CollectDecVars
mutual

partial def IneqCnstr.collectDecVars (c' : IneqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .notCore .. | .coreOfNat .. | .notCoreOfNat .. | .ring .. | .ringEq ..
  | .oneGtZero | .ofEq .. | .ofEqOfNat .. => return ()
  | .combine c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .norm c₁ _ => c₁.collectDecVars
  | .dec h => markAsFound h
  | .ofDiseqSplit (decVars := decVars) .. => decVars.forM markAsFound
  | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

-- `DiseqCnstr` is currently mutually recursive with `IneqCnstr`, but it will be in the future.
-- Actually, it cannot even contain decision variables in the current implementation.
partial def DiseqCnstr.collectDecVars (c' : DiseqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .coreOfNat .. | .oneNeZero | .ring .. => return ()
  | .neg c => c.collectDecVars
  | .subst _ _ c₁ c₂ | .subst1 _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def EqCnstr.collectDecVars (c' : EqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .core .. | .coreCommRing .. | .coreOfNat .. => return ()
  | .neg c | .coeff _ c => c.collectDecVars

end

def UnsatProof.collectDecVars (h : UnsatProof) : CollectDecVarsM Unit := do
  match h with
  | .lt c | .diseq c => c.collectDecVars

end Lean.Meta.Grind.Arith.Linear
