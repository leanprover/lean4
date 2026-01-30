/-
Copyright (c) 2018 Johannes Hölzl, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Johannes Hölzl, David Renshaw, Wojciech Różowski
-/

module

prelude

public import Lean.Meta.Basic
import Lean.Elab.Term.TermElabM
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Cases


namespace Lean.Meta

open Lean Meta Elab

/-- Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
private def MVarId.existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (fun mv e ↦ do
      let (subgoals,_) ← Elab.Term.TermElabM.run <| Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

/--
Apply the `n`-th constructor of the target type,
checking that it is an inductive type,
and that there are the expected number of constructors.
-/
private def MVarId.nthConstructor
    (name : Name) (idx : Nat) (expected? : Option Nat := none) (goal : MVarId) :
    MetaM (List MVarId) := do
  goal.withContext do
    goal.checkNotAssigned name
    matchConstInduct (← goal.getType').getAppFn
      (fun _ => throwTacticEx name goal "target is not an inductive datatype")
      fun ival us => do
        if let some e := expected? then unless ival.ctors.length == e do
          throwTacticEx name goal
            s!"{name} tactic works for inductive types with exactly {e} constructors"
        if h : idx < ival.ctors.length then
          goal.apply <| mkConst ival.ctors[idx] us
        else
          throwTacticEx name goal s!"index {idx} out of bounds, only {ival.ctors.length} constructors"

/-- `select m n` runs `right` `m` times; if `m < n`, then it also runs `left` once.
Fails if `n < m`. -/
private def select (m n : Nat) (goal : MVarId) : MetaM MVarId :=
  match m,n with
  | 0, 0             => pure goal
  | 0, (_ + 1)       => do
    let [new_goal] ← MVarId.nthConstructor `left 0 (some 2) goal
      | throwError "expected only one new goal"
    pure new_goal
  | (m + 1), (n + 1) => do
    let [new_goal] ← MVarId.nthConstructor `right 1 (some 2) goal
      | throwError "expected only one new goal"
    select m n new_goal
  | _, _             => failure

/-- `compactRelation bs as_ps`: Produce a relation of the form:
```lean
R := fun as ↦ ∃ bs, ⋀_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.
-/
private partial def compactRelation :
    List Expr → List (Expr × Expr) → List (Option Expr) × List (Expr × Expr) × (Expr → Expr)
| [],    as_ps => ([], as_ps, id)
| b::bs, as_ps =>
  match as_ps.span (fun ⟨_, p⟩ ↦ p != b) with
    | (_, []) => -- found nothing in ps equal to b
      let (bs, as_ps', subst) := compactRelation bs as_ps
      (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e ↦ e.replaceFVar b a
      let (bs, as_ps', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ ↦ (a, i p)))
      (none :: bs, as_ps', i ∘ subst)

private def updateLambdaBinderInfoD! (e : Expr) : Expr :=
  match e with
  | .lam n domain body _ => .lam n domain body .default
  | _           => panic! "lambda expected"

/-- Generates an expression of the form `∃ (args), inner`. `args` is assumed to be a list of fvars.
When possible, `p ∧ q` is used instead of `∃ (_ : p), q`. -/
private def mkExistsList (args : List Expr) (inner : Expr) : MetaM Expr :=
  args.foldrM
    (fun arg i:Expr => do
      let t ← inferType arg
      let l := (← inferType t).sortLevel!
      if arg.occurs i || l != Level.zero
        then pure (mkApp2 (.const `Exists [l]) t
          (updateLambdaBinderInfoD! <| ← mkLambdaFVars #[arg] i))
        else pure <| mkApp2 (mkConst `And) t i)
    inner

/-- `mkOpList op empty [x1, x2, ...]` is defined as `op x1 (op x2 ...)`.
  Returns `empty` if the list is empty. -/
private def mkOpList (op : Expr) (empty : Expr) : List Expr → Expr
  | []        => empty
  | [e]       => e
  | (e :: es) => mkApp2 op e <| mkOpList op empty es

/-- `mkAndList [x1, x2, ...]` is defined as `x1 ∧ (x2 ∧ ...)`, or `True` if the list is empty. -/
private def mkAndList : List Expr → Expr := mkOpList (mkConst `And) (mkConst `True)

/-- `mkOrList [x1, x2, ...]` is defined as `x1 ∨ (x2 ∨ ...)`, or `False` if the list is empty. -/
private def mkOrList : List Expr → Expr := mkOpList (mkConst `Or) (mkConst `False)

/-- Drops the final element of a list. -/
private def List.init : List α → List α
  | []     => []
  | [_]    => []
  | a::l => a::init l

/-- Auxiliary data associated with a single constructor of an inductive declaration.
-/
private structure Shape : Type where
  /-- For each forall-bound variable in the type of the constructor, minus
  the "params" that apply to the entire inductive type, this list contains `true`
  if that variable has been kept after `compactRelation`.

  For example, `List.Chain.nil` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a : α}, List.Chain R a []`
  ```
  and the first two variables `α` and `R` are "params", while the `a : α` gets
  eliminated in a `compactRelation`, so `variablesKept = [false]`.

  `List.Chain.cons` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l : List α},
       R a b → List.Chain R b l → List.Chain R a (b :: l)
  ```
  and the `a : α` gets eliminated, so `variablesKept = [false,true,true,true,true]`.
  -/
  variablesKept : List Bool

  /-- The number of equalities, or `none` in the case when we've reduced something
  of the form `p ∧ True` to just `p`.
  -/
  neqs : Option Nat

/-- Converts an inductive constructor `c` into a `Shape` that will be used later in
while proving the iff theorem, and a proposition representing the constructor.
-/
private def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
    MetaM (Shape × Expr) := do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty ↦ do
    pure <| ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty ↦ do
    let idxs_inst := ty.getAppArgs.toList.drop params.length
    let (bs, eqs, subst) := compactRelation fvars.toList (idxs.zip idxs_inst)
    let eqs ← eqs.mapM (fun ⟨idx, inst⟩ ↦ do
      let ty ← idx.fvarId!.getType
      let instTy ← inferType inst
      let u := (← inferType ty).sortLevel!
      if ← isDefEq ty instTy
      then pure (mkApp3 (.const `Eq [u]) ty idx inst)
      else pure (mkApp4 (.const `HEq [u]) ty idx instTy inst))
    let (n, r) ← match bs.filterMap id, eqs with
    | [], [] => do
      pure (some 0, (mkConst `True))
    | bs', [] => do
      let t : Expr ← bs'.getLast!.fvarId!.getType
      let l := (← inferType t).sortLevel!
      if l == Level.zero then do
        let r ← mkExistsList (List.init bs') t
        pure (none, subst r)
      else do
        let r ← mkExistsList bs' (mkConst `True)
        pure (some 0, subst r)
    | bs', _ => do
      let r ← mkExistsList bs' (mkAndList eqs)
      pure (some eqs.length, subst r)
    pure (⟨bs.map Option.isSome, n⟩, r)

/-- Splits the goal `n` times via `refine ⟨?_,?_⟩`, and then applies `constructor` to
close the resulting subgoals.
-/
private def splitThenConstructor (mvar : MVarId) (n : Nat) : MetaM Unit :=
match n with
| 0   => do
  let (subgoals',_) ← Term.TermElabM.run <| Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n + 1 => do
  let (subgoals,_) ← Term.TermElabM.run <| Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
  let (subgoals',_) ← Term.TermElabM.run <| Tactic.run sg1 do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  splitThenConstructor sg2 n

/-- Proves the left to right direction of a generated iff theorem.
`shape` is the output of a call to `constrToProp`.
-/
private def toCases (mvar : MVarId) (shape : List Shape) : MetaM Unit :=
do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ ↦ do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ ↦ if c then some v else none)
    let mvar'' ← select p (subgoals.size - 1) subgoal.mvarId
    match t with
    | none => do
      let v := vars[shape.length - 1]!
      let mv ← MVarId.existsi mvar'' (List.init si)
      mv.assign v
    | some n => do
      let mv ← MVarId.existsi mvar'' si
      splitThenConstructor mv (n - 1)
  pure ()

/-- Calls `cases` on `h` (assumed to be a binary sum) `n` times, and returns
the resulting subgoals and their corresponding new hypotheses.
-/
def nCasesSum (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (List (FVarId × MVarId)) :=
match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2.mvarId fvar2
  pure ((fvar1, sg1.mvarId)::rest)

/-- Calls `cases` on `h` (assumed to be a binary product) `n` times, and returns
the resulting subgoal and the new hypotheses.
-/
private def nCasesProd (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (MVarId × List FVarId) :=
match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

/--
Iterate over two lists, if the first element of the first list is `false`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
listBoolMerge [false, true, false, true] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
private def listBoolMerge : List Bool → List α → List (Option α)
  | [], _ => []
  | false :: xs, ys => none :: listBoolMerge xs ys
  | true :: xs, y :: ys => some y :: listBoolMerge xs ys
  | true :: _, [] => []

/-- Proves the right to left direction of a generated iff theorem.
-/
private def toInductive (mvar : MVarId) (cs : List Name)
    (gs : List Expr) (s : List Shape) (h : FVarId) :
    MetaM Unit := do
  match s.length with
  | 0       => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constr_name, ⟨h, mv⟩, bs, e⟩ ↦ do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← match e with
        | none =>
            let (id, fvarIds) ← nCasesProd (n-1) mv h
            pure ⟨id, fvarIds⟩
        | some 0 => do let ⟨mvar', fvars⟩ ← nCasesProd n mv h
                          let mvar'' ← mvar'.tryClear fvars.getLast!
                          pure ⟨mvar'', fvars⟩
        | some (e + 1) => do
          let (mv', fvars) ← nCasesProd n mv h
          let lastfv := fvars.getLast!
          let (mv2, fvars') ← nCasesProd e mv' lastfv

          /- `fvars'.foldlM subst mv2` fails when we have dependent equalities (`HEq`).
          `subst` will change the dependent hypotheses, so that the `uniq` local names
          are wrong afterwards. Instead we revert them and pull them out one-by-one. -/
          let (_, mv3) ← mv2.revert fvars'.toArray
          let mv4 ← fvars'.foldlM (fun mv _ ↦ do
            let ⟨fv, mv'⟩ ← mv.intro1
            let #[res] ← mv'.cases fv | throwError "expected one case subgoal"
            return res.mvarId) mv3
          pure (mv4, fvars)
        mvar'.withContext do
          let fvarIds := (← getLCtx).getFVarIds.toList
          let gs := fvarIds.take gs.length
          let m := gs.map some ++ listBoolMerge bs _fvars
          let args ← m.mapM fun a ↦
            match a with
            | some v => pure (mkFVar v)
            | none => mkFreshExprMVar none
          let c ← mkConstWithLevelParams constr_name
          let e := mkAppN c args.toArray
          let t ← inferType e
          let mt ← mvar'.getType
          let _ ← isDefEq t mt -- infer values for those mvars we just made
          mvar'.assign e

/--
  Generates existential form of a prop-valued inductive type and proves the equivalence.
-/
private def mkIffOfInductivePropImpl (inductVal : InductiveVal) (rel : Name) : MetaM Unit := do
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /- we use these names for our universe parameters, maybe we should construct a copy of them
  using `uniq_name` -/

  let (thmTy, shape, existential) ← Meta.forallTelescopeReducing type fun fvars ty ↦ do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst inductVal.name univs) fvars
    let fvars' := fvars.toList
    let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shape_rhss.unzip
    let existential := mkOrList rhss
    let existential ← mkLambdaFVars fvars existential
    pure (← mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrList rhss)), shape, existential)

  trace[Meta.MkIffOfInductiveProp] "Existential form is: {existential}"
  trace[Meta.MkIffOfInductiveProp] "The type of proof of equivalence: {thmTy}"

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  toCases mp shape
  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  let proof ← instantiateMVars mvar
  addDecl <| (←mkThmOrUnsafeDef {
    name := rel
    levelParams := univNames
    type := thmTy
    value := proof
  })

  addDecl <| .defnDecl (←mkDefinitionValInferringUnsafe
    (inductVal.name ++ `existential) inductVal.levelParams
    (←inferType existential) existential .opaque)


public def mkSumOfProducts (declName : Name) : MetaM Unit := do
    trace[Meta.MkIffOfInductiveProp] "Generating existential form of {declName}"
    let .inductInfo infos ← getConstInfo declName | throwError "Needs to be a definition"
    mkIffOfInductivePropImpl infos (declName ++ `existential_equiv)

builtin_initialize
  registerTraceClass `Meta.MkIffOfInductiveProp

end Lean.Meta
