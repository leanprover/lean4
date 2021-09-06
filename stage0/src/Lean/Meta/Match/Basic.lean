/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Check
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.CaseArraySizes

namespace Lean.Meta.Match

/--
  Auxiliary annotation used to mark terms marked with the "inaccessible" annotation `.(t)` and
  `_` in patterns. -/
def mkInaccessible (e : Expr) : Expr :=
  mkAnnotation `_inaccessible e

def inaccessible? (e : Expr) : Option Expr :=
  annotation? `_inaccessible e

inductive Pattern : Type where
  | inaccessible (e : Expr) : Pattern
  | var          (fvarId : FVarId) : Pattern
  | ctor         (ctorName : Name) (us : List Level) (params : List Expr) (fields : List Pattern) : Pattern
  | val          (e : Expr) : Pattern
  | arrayLit     (type : Expr) (xs : List Pattern) : Pattern
  | as           (varId : FVarId) (p : Pattern) : Pattern
  deriving Inhabited

namespace Pattern

partial def toMessageData : Pattern → MessageData
  | inaccessible e         => m!".({e})"
  | var varId              => mkFVar varId
  | ctor ctorName _ _ []   => ctorName
  | ctor ctorName _ _ pats => m!"({ctorName}{pats.foldl (fun (msg : MessageData) pat => msg ++ " " ++ toMessageData pat) Format.nil})"
  | val e                  => e
  | arrayLit _ pats        => m!"#[{MessageData.joinSep (pats.map toMessageData) ", "}]"
  | as varId p             => m!"{mkFVar varId}@{toMessageData p}"

partial def toExpr (p : Pattern) (annotate := false) : MetaM Expr :=
  visit p
where
  visit (p : Pattern) := do
    match p with
    | inaccessible e                 =>
      if annotate then
        pure (mkInaccessible e)
      else
        pure e
    | var fvarId                     => pure $ mkFVar fvarId
    | val e                          => pure e
    | as fvarId p                    =>
      if annotate then
        mkAppM `namedPattern #[mkFVar fvarId, (← visit p)]
      else
        visit p
    | arrayLit type xs               =>
      let xs ← xs.mapM visit
      mkArrayLit type xs
    | ctor ctorName us params fields =>
      let fields ← fields.mapM visit
      pure $ mkAppN (mkConst ctorName us) (params ++ fields).toArray

/- Apply the free variable substitution `s` to the given pattern -/
partial def applyFVarSubst (s : FVarSubst) : Pattern → Pattern
  | inaccessible e  => inaccessible $ s.apply e
  | ctor n us ps fs => ctor n us (ps.map s.apply) $ fs.map (applyFVarSubst s)
  | val e           => val $ s.apply e
  | arrayLit t xs   => arrayLit (s.apply t) $ xs.map (applyFVarSubst s)
  | var fvarId      => match s.find? fvarId with
    | some e => inaccessible e
    | none   => var fvarId
  | as fvarId p     => match s.find? fvarId with
    | none   => as fvarId $ applyFVarSubst s p
    | some _ => applyFVarSubst s p

def replaceFVarId (fvarId : FVarId) (v : Expr) (p : Pattern) : Pattern :=
  let s : FVarSubst := {}
  p.applyFVarSubst (s.insert fvarId v)

partial def hasExprMVar : Pattern → Bool
  | inaccessible e => e.hasExprMVar
  | ctor _ _ ps fs => ps.any (·.hasExprMVar) || fs.any hasExprMVar
  | val e          => e.hasExprMVar
  | as _ p         => hasExprMVar p
  | arrayLit t xs  => t.hasExprMVar || xs.any hasExprMVar
  | _              => false

end Pattern

partial def instantiatePatternMVars : Pattern → MetaM Pattern
  | Pattern.inaccessible e      => return Pattern.inaccessible (← instantiateMVars e)
  | Pattern.val e               => return Pattern.val (← instantiateMVars e)
  | Pattern.ctor n us ps fields => return Pattern.ctor n us (← ps.mapM instantiateMVars) (← fields.mapM instantiatePatternMVars)
  | Pattern.as x p              => return Pattern.as x (← instantiatePatternMVars p)
  | Pattern.arrayLit t xs       => return Pattern.arrayLit (← instantiateMVars t) (← xs.mapM instantiatePatternMVars)
  | p                   => return p

structure AltLHS where
  ref        : Syntax
  fvarDecls  : List LocalDecl -- Free variables used in the patterns.
  patterns   : List Pattern   -- We use `List Pattern` since we have nary match-expressions.

def instantiateAltLHSMVars (altLHS : AltLHS) : MetaM AltLHS :=
  return { altLHS with
    fvarDecls := (← altLHS.fvarDecls.mapM instantiateLocalDeclMVars),
    patterns  := (← altLHS.patterns.mapM instantiatePatternMVars)
  }

structure Alt where
  ref       : Syntax
  idx       : Nat -- for generating error messages
  rhs       : Expr
  fvarDecls : List LocalDecl
  patterns  : List Pattern
  deriving Inhabited

namespace Alt

partial def toMessageData (alt : Alt) : MetaM MessageData := do
  withExistingLocalDecls alt.fvarDecls do
    let msg : List MessageData := alt.fvarDecls.map fun d => m!"{d.toExpr}:({d.type})"
    let msg : MessageData := m!"{msg} |- {alt.patterns.map Pattern.toMessageData} => {alt.rhs}"
    addMessageContext msg

def applyFVarSubst (s : FVarSubst) (alt : Alt) : Alt :=
  { alt with
    patterns  := alt.patterns.map fun p => p.applyFVarSubst s,
    fvarDecls := alt.fvarDecls.map fun d => d.applyFVarSubst s,
    rhs       := alt.rhs.applyFVarSubst s }

def replaceFVarId (fvarId : FVarId) (v : Expr) (alt : Alt) : Alt :=
  { alt with
    patterns  := alt.patterns.map fun p => p.replaceFVarId fvarId v,
    fvarDecls :=
      let decls := alt.fvarDecls.filter fun d => d.fvarId != fvarId
      decls.map $ replaceFVarIdAtLocalDecl fvarId v,
    rhs       := alt.rhs.replaceFVarId fvarId v }

/-
  Similar to `checkAndReplaceFVarId`, but ensures type of `v` is definitionally equal to type of `fvarId`.
  This extra check is necessary when performing dependent elimination and inaccessible terms have been used.
  For example, consider the following code fragment:

```
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)

inductive VecPred {α : Type u} (P : α → Prop) : {n : Nat} → Vec α n → Prop where
  | nil   : VecPred P Vec.nil
  | cons  {n : Nat} {head : α} {tail : Vec α n} : P head → VecPred P tail → VecPred P (Vec.cons head tail)

theorem ex {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
  | _, Vec.cons head _, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩
```
Recall that `_` in a pattern can be elaborated into pattern variable or an inaccessible term.
The elaborator uses an inaccessible term when typing constraints restrict its value.
Thus, in the example above, the `_` at `Vec.cons head _` becomes the inaccessible pattern `.(Vec.nil)`
because the type ascription `(w : VecPred P Vec.nil)` propagates typing constraints that restrict its value to be `Vec.nil`.
After elaboration the alternative becomes:
```
  | .(0), @Vec.cons .(α) .(0) head .(Vec.nil), @VecPred.cons .(α) .(P) .(0) .(head) .(Vec.nil) h w => ⟨head, h⟩
```
where
```
(head : α), (h: P head), (w : VecPred P Vec.nil)
```
Then, when we process this alternative in this module, the following check will detect that
`w` has type `VecPred P Vec.nil`, when it is supposed to have type `VecPred P tail`.
Note that if we had written
```
theorem ex {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
  | _, Vec.cons head Vec.nil, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩
```
we would get the easier to digest error message
```
missing cases:
_, (Vec.cons _ _ (Vec.cons _ _ _)), _
```
-/
def checkAndReplaceFVarId (fvarId : FVarId) (v : Expr) (alt : Alt) : MetaM Alt := do
  match alt.fvarDecls.find? fun (fvarDecl : LocalDecl) => fvarDecl.fvarId == fvarId with
  | none          => throwErrorAt alt.ref "unknown free pattern variable"
  | some fvarDecl => do
    let vType ← inferType v
    unless (← isDefEqGuarded fvarDecl.type vType) do
      withExistingLocalDecls alt.fvarDecls do
        let (expectedType, givenType) ← addPPExplicitToExposeDiff vType fvarDecl.type
        throwErrorAt alt.ref "type mismatch during dependent match-elimination at pattern variable '{mkFVar fvarDecl.fvarId}' with type{indentExpr givenType}\nexpected type{indentExpr expectedType}"
    pure $ replaceFVarId fvarId v alt

end Alt

inductive Example where
  | var        : FVarId → Example
  | underscore : Example
  | ctor       : Name → List Example → Example
  | val        : Expr → Example
  | arrayLit   : List Example → Example

namespace Example

partial def replaceFVarId (fvarId : FVarId) (ex : Example) : Example → Example
  | var x        => if x == fvarId then ex else var x
  | ctor n exs   => ctor n $ exs.map (replaceFVarId fvarId ex)
  | arrayLit exs => arrayLit $ exs.map (replaceFVarId fvarId ex)
  | ex           => ex

partial def applyFVarSubst (s : FVarSubst) : Example → Example
  | var fvarId =>
    match s.get fvarId with
    | Expr.fvar fvarId' _ => var fvarId'
    | _                   => underscore
  | ctor n exs   => ctor n $ exs.map (applyFVarSubst s)
  | arrayLit exs => arrayLit $ exs.map (applyFVarSubst s)
  | ex           => ex

partial def varsToUnderscore : Example → Example
  | var x        => underscore
  | ctor n exs   => ctor n $ exs.map varsToUnderscore
  | arrayLit exs => arrayLit $ exs.map varsToUnderscore
  | ex           => ex

partial def toMessageData : Example → MessageData
  | var fvarId        => mkFVar fvarId
  | ctor ctorName []  => mkConst ctorName
  | ctor ctorName exs => m!"({mkConst ctorName}{exs.foldl (fun msg pat => m!"{msg} {toMessageData pat}") Format.nil})"
  | arrayLit exs      => "#" ++ MessageData.ofList (exs.map toMessageData)
  | val e             => e
  | underscore        => "_"

end Example

def examplesToMessageData (cex : List Example) : MessageData :=
  MessageData.joinSep (cex.map (Example.toMessageData ∘ Example.varsToUnderscore)) ", "

structure Problem where
  mvarId        : MVarId
  vars          : List Expr
  alts          : List Alt
  examples      : List Example
  deriving Inhabited

def withGoalOf {α} (p : Problem) (x : MetaM α) : MetaM α :=
  withMVarContext p.mvarId x

def Problem.toMessageData (p : Problem) : MetaM MessageData :=
  withGoalOf p do
    let alts ← p.alts.mapM Alt.toMessageData
    let vars ← p.vars.mapM fun x => do let xType ← inferType x; pure m!"{x}:({xType})"
    return m!"remaining variables: {vars}\nalternatives:{indentD (MessageData.joinSep alts Format.line)}\nexamples:{examplesToMessageData p.examples}\n"

abbrev CounterExample := List Example

def counterExampleToMessageData (cex : CounterExample) : MessageData :=
  examplesToMessageData cex

def counterExamplesToMessageData (cexs : List CounterExample) : MessageData :=
  MessageData.joinSep (cexs.map counterExampleToMessageData) Format.line

structure MatcherResult where
  matcher         : Expr -- The matcher. It is not just `Expr.const matcherName` because the type of the major premises may contain free variables.
  counterExamples : List CounterExample
  unusedAltIdxs   : List Nat
  addMatcher      : MetaM Unit

/--
  Convert a expression occurring as the argument of a `match` motive application back into a `Pattern`
  For example, we can use this method to convert `x::y::xs` at
  ```
  ...
  (motive : List Nat → Sort u_1) (xs : List Nat) (h_1 : (x y : Nat) → (xs : List Nat) → motive (x :: y :: xs))
  ...
  ```
  into a pattern object
-/
partial def toPattern (e : Expr) : MetaM Pattern := do
  match inaccessible? e with
  | some t => return Pattern.inaccessible t
  | none =>
    match e.arrayLit? with
    | some (α, lits) =>
      return Pattern.arrayLit α (← lits.mapM toPattern)
    | none =>
      if e.isAppOfArity `namedPattern 3 then
        let p ← toPattern <| e.getArg! 2
        match e.getArg! 1 with
        | Expr.fvar fvarId _ => return Pattern.as fvarId p
        | _                  => throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
      else if isMatchValue e then
        return Pattern.val e
      else if e.isFVar then
        return Pattern.var e.fvarId!
      else
        let newE ← whnf e
        if newE != e then
          toPattern newE
        else matchConstCtor e.getAppFn (fun _ => throwError "unexpected pattern{indentExpr e}") fun v us => do
          let args := e.getAppArgs
          unless args.size == v.numParams + v.numFields do
            throwError "unexpected pattern{indentExpr e}"
          let params := args.extract 0 v.numParams
          let fields := args.extract v.numParams args.size
          let fields ← fields.mapM toPattern
          return Pattern.ctor v.name us params.toList fields.toList

end Lean.Meta.Match
