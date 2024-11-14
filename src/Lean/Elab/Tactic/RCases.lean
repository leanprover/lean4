/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jacob von Raumer
-/
prelude
import Lean.Elab.Tactic.Induction

namespace Lean.Elab.Tactic.RCases
open Meta Parser Tactic

/--
Enables the 'unused rcases pattern' linter. This will warn when a pattern is ignored by
`rcases`, `rintro`, `ext` and similar tactics.
-/
register_option linter.unusedRCasesPattern : Bool := {
  defValue := true
  descr := "enable the 'unused rcases pattern' linter"
}

instance : Coe Ident (TSyntax `rcasesPat) where
  coe stx := Unhygienic.run `(rcasesPat| $stx:ident)
instance : Coe (TSyntax `rcasesPat) (TSyntax ``rcasesPatMed) where
  coe stx := Unhygienic.run `(rcasesPatMed| $stx:rcasesPat)
instance : Coe (TSyntax ``rcasesPatMed) (TSyntax ``rcasesPatLo) where
  coe stx := Unhygienic.run `(rcasesPatLo| $stx:rcasesPatMed)
instance : Coe (TSyntax `rcasesPat) (TSyntax `rintroPat) where
  coe stx := Unhygienic.run `(rintroPat| $stx:rcasesPat)

/-- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
local notation "ListΣ" => List

/-- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
local notation "ListΠ" => List

/--
An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A hyphen `-`, which clears the active hypothesis and any dependents.
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
inductive RCasesPatt : Type
  /-- A parenthesized expression, used for hovers -/
  | paren (ref : Syntax) : RCasesPatt → RCasesPatt
  /-- A named pattern like `foo` -/
  | one (ref : Syntax) : Name → RCasesPatt
  /-- A hyphen `-`, which clears the active hypothesis and any dependents. -/
  | clear (ref : Syntax) : RCasesPatt
  /-- An explicit pattern `@pat`. -/
  | explicit (ref : Syntax) : RCasesPatt → RCasesPatt
  /-- A type ascription like `pat : ty` (parentheses are optional) -/
  | typed (ref : Syntax) : RCasesPatt → Term → RCasesPatt
  /-- A tuple constructor like `⟨p1, p2, p3⟩` -/
  | tuple (ref : Syntax) : ListΠ RCasesPatt → RCasesPatt
  /-- An alternation / variant pattern `p1 | p2 | p3` -/
  | alts (ref : Syntax) : ListΣ RCasesPatt → RCasesPatt
  deriving Repr

namespace RCasesPatt

instance : Inhabited RCasesPatt := ⟨RCasesPatt.one Syntax.missing `_⟩

/-- Get the name from a pattern, if provided -/
partial def name? : RCasesPatt → Option Name
  | one _ `_    => none
  | one _ `rfl  => none
  | one _ n     => n
  | paren _ p
  | typed _ p _
  | alts _ [p]  => p.name?
  | _           => none

/-- Get the syntax node from which this pattern was parsed. Used for error messages -/
def ref : RCasesPatt → Syntax
  | paren ref _
  | one ref _
  | clear ref
  | explicit ref _
  | typed ref _ _
  | tuple ref _
  | alts ref _ => ref

/--
Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩` if `p` is not already a tuple.
-/
def asTuple : RCasesPatt → Bool × ListΠ RCasesPatt
  | paren _ p    => p.asTuple
  | explicit _ p => (true, p.asTuple.2)
  | tuple _ ps   => (false, ps)
  | p            => (false, [p])

/--
Interpret an rcases pattern as an alternation, where non-alternations are treated as one
alternative.
-/
def asAlts : RCasesPatt → ListΣ RCasesPatt
  | paren _ p => p.asAlts
  | alts _ ps => ps
  | p         => [p]

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
def typed? (ref : Syntax) : RCasesPatt → Option Term → RCasesPatt
  | p, none => p
  | p, some ty => typed ref p ty

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
def tuple' : ListΠ RCasesPatt → RCasesPatt
  | [p] => p
  | ps  => tuple (ps.head?.map (·.ref) |>.getD .missing) ps

/--
Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
a unary alternation `|p`.
-/
def alts' (ref : Syntax) : ListΣ RCasesPatt → RCasesPatt
  | [p] => p
  | ps  => alts ref ps

/--
This function is used for producing rcases patterns based on a case tree. Suppose that we have
a list of patterns `ps` that will match correctly against the branches of the case tree for one
constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.

We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
nested match).
-/
def tuple₁Core : ListΠ RCasesPatt → ListΠ RCasesPatt
  | []         => []
  | [tuple ref []] => [tuple ref []]
  | [tuple _ ps] => ps
  | p :: ps    => p :: tuple₁Core ps

/--
This function is used for producing rcases patterns based on a case tree. This is like
`tuple₁Core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`.
-/
def tuple₁ : ListΠ RCasesPatt → RCasesPatt
  | []      => default
  | [one ref n] => one ref n
  | ps      => tuple ps.head!.ref $ tuple₁Core ps

/--
This function is used for producing rcases patterns based on a case tree. Here we are given
the list of patterns to apply to each argument of each constructor after the main case, and must
produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
`a | b | (c | d)`.
-/
def alts₁Core : ListΣ (ListΠ RCasesPatt) → ListΣ RCasesPatt
  | []          => []
  | [[alts _ ps]] => ps
  | p :: ps     => tuple₁ p :: alts₁Core ps

/--
This function is used for producing rcases patterns based on a case tree. This is like
`alts₁Core`, but it produces a cases pattern directly instead of a list of alternatives. We
specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
don't have any syntax for unary alternation). Otherwise we can use the regular merging of
alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`.
-/
def alts₁ (ref : Syntax) : ListΣ (ListΠ RCasesPatt) → RCasesPatt
  | [[]]        => tuple .missing []
  | [[alts ref ps]] => tuple ref ps
  | ps          => alts' ref $ alts₁Core ps

open MessageData in
partial instance : ToMessageData RCasesPatt := ⟨fmt 0⟩ where
  /-- parenthesize the message if the precedence is above `tgt` -/
  parenAbove (tgt p : Nat) (m : MessageData) : MessageData :=
    if tgt < p then m.paren else m
  /-- format an `RCasesPatt` with the given precedence: 0 = lo, 1 = med, 2 = hi -/
  fmt : Nat → RCasesPatt → MessageData
  | p, paren _ pat => fmt p pat
  | _, one _ n => n
  | _, clear _ => "-"
  | _, explicit _ pat => m!"@{fmt 2 pat}"
  | p, typed _ pat ty => parenAbove 0 p m!"{fmt 1 pat}: {ty}"
  | _, tuple _ pats => bracket "⟨" (joinSep (pats.map (fmt 0)) ("," ++ Format.line)) "⟩"
  | p, alts _ pats => parenAbove 1 p (joinSep (pats.map (fmt 2)) " | ")

end RCasesPatt

/--
Takes the number of fields of a single constructor and patterns to match its fields against
(not necessarily the same number). The returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
tactics.
-/
def processConstructor (ref : Syntax) (info : Array ParamInfo)
    (explicit : Bool) (idx : Nat) (ps : ListΠ RCasesPatt) : ListΠ Name × ListΠ RCasesPatt :=
  if _ : idx < info.size then
    if !explicit && info[idx].binderInfo != .default then
      let (ns, tl) := processConstructor ref info explicit (idx+1) ps
      (`_ :: ns, default :: tl)
    else if idx+1 < info.size then
      let p := ps.headD default
      let (ns, tl) := processConstructor ref info explicit (idx+1) (ps.tailD [])
      (p.name?.getD `_ :: ns, p :: tl)
    else match ps with
      | []  => ([`_], [default])
      | [p] => ([p.name?.getD `_], [p])
      | ps  => ([`_], [(bif explicit then .explicit ref else id) (.tuple ref ps)])
  else ([], [])
termination_by info.size - idx

/--
Takes a list of constructor names, and an (alternation) list of patterns, and matches each
pattern against its constructor. It returns the list of names that will be passed to `cases`,
and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
(conjunctive) list of patterns to apply to each constructor argument.
-/
def processConstructors (ref : Syntax) (params : Nat) (altVarNames : Array AltVarNames := #[]) :
    ListΣ Name → ListΣ RCasesPatt → MetaM (Array AltVarNames × ListΣ (Name × ListΠ RCasesPatt))
  | [], _ => pure (altVarNames, [])
  | c :: cs, ps => do
    let info := (← getFunInfo (← mkConstWithLevelParams c)).paramInfo
    let p := ps.headD default
    let t := ps.tailD []
    let ((explicit, h), t) := match cs, t with
    | [], _ :: _ => ((false, [RCasesPatt.alts ref ps]), [])
    | _,  _      => (p.asTuple, t)
    let (ns, ps) := processConstructor p.ref info explicit params h
    let (altVarNames, r) ← processConstructors ref params (altVarNames.push ⟨true, ns⟩) cs t
    pure (altVarNames, (c, ps) :: r)

open Elab Tactic

-- TODO(Mario): this belongs in core
/-- Like `Lean.Meta.subst`, but preserves the `FVarSubst`. -/
def subst' (goal : MVarId) (hFVarId : FVarId)
    (fvarSubst : FVarSubst := {}) : MetaM (FVarSubst × MVarId) := do
  let hLocalDecl ← hFVarId.getDecl
  let error {α} _ : MetaM α := throwTacticEx `subst goal
    m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr hLocalDecl.type}"
  let some (_, lhs, rhs) ← matchEq? hLocalDecl.type | error ()
  let substReduced (newType : Expr) (symm : Bool) : MetaM (FVarSubst × MVarId) := do
    let goal ← goal.assert hLocalDecl.userName newType (mkFVar hFVarId)
    let (hFVarId', goal) ← goal.intro1P
    let goal ← goal.clear hFVarId
    substCore goal hFVarId' (symm := symm) (tryToSkip := true) (fvarSubst := fvarSubst)
  let rhs' ← whnf rhs
  if rhs'.isFVar then
    if rhs != rhs' then
      substReduced (← mkEq lhs rhs') true
    else
      substCore goal hFVarId (symm := true) (tryToSkip := true) (fvarSubst := fvarSubst)
  else
    let lhs' ← whnf lhs
    if lhs'.isFVar then
      if lhs != lhs' then
        substReduced (← mkEq lhs' rhs) false
      else
        substCore goal hFVarId (symm := false) (tryToSkip := true) (fvarSubst := fvarSubst)
    else error ()

mutual

/--
This will match a pattern `pat` against a local hypothesis `e`.
* `g`: The initial subgoal
* `fs`: A running variable substitution, the result of `cases` operations upstream.
  The variable `e` must be run through this map before locating it in the context of `g`,
  and the output variable substitutions will be end extensions of this one.
* `clears`: The list of variables to clear in all subgoals generated from this point on.
  We defer clear operations because clearing too early can cause `cases` to fail.
  The actual clearing happens in `RCases.finish`.
* `e`: a local hypothesis, the scrutinee to match against.
* `a`: opaque "user data" which is passed through all the goal calls at the end.
* `pat`: the pattern to match against
* `cont`: A continuation. This is called on every goal generated by the result of the pattern
  match, with updated values for `g` , `fs`, `clears`, and `a`.
-/
partial def rcasesCore (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (e : Expr) (a : α)
    (pat : RCasesPatt) (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) :
    TermElabM α := do
  let asFVar : Expr → MetaM _
    | .fvar e => pure e
    | e => throwError "rcases tactic failed: {e} is not a fvar"
  withRef pat.ref <| g.withContext do match pat with
  | .one ref `rfl =>
    Term.synthesizeSyntheticMVarsNoPostponing
    -- Note: the mdata prevents the span from getting highlighted like a variable
    Term.addTermInfo' ref (.mdata {} e)
    let (fs, g) ← subst' g (← asFVar (fs.apply e)) fs
    cont g fs clears a
  | .one ref _ =>
    if e.isFVar then
      Term.addLocalVarInfo ref e
    cont g fs clears a
  | .clear ref =>
    Term.addTermInfo' ref (.mdata {} e)
    cont g fs (if let .fvar e := e then clears.push e else clears) a
  | .typed ref pat ty =>
    Term.addTermInfo' ref (.mdata {} e)
    let expected ← Term.elabType ty
    let e := fs.apply e
    let etype ← inferType e
    unless ← isDefEq etype expected do
      Term.throwTypeMismatchError "rcases: scrutinee" expected etype e
    let g ← if let .fvar e := e then g.replaceLocalDeclDefEq e expected else pure g
    rcasesCore g fs clears e a pat cont
  | .paren ref p
  | .alts ref [p] =>
    Term.addTermInfo' ref (.mdata {} e)
    rcasesCore g fs clears e a p cont
  | _ =>
    Term.addTermInfo' pat.ref (.mdata {} e)
    let e := fs.apply e
    let _ ← asFVar e
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← whnfD (← inferType e)
    let failK {α} _ : TermElabM α :=
      throwError "rcases tactic failed: {e} : {type} is not an inductive datatype"
    let (r, subgoals) ← matchConst type.getAppFn failK fun
      | ConstantInfo.quotInfo info, _ => do
        unless info.kind matches QuotKind.type do failK ()
        let pat := pat.asAlts.headD default
        let (explicit, pat₁) := pat.asTuple
        let ([x], ps) := processConstructor pat.ref #[{}] explicit 0 pat₁ | unreachable!
        let (vars, g) ← g.revert (← getFVarsToGeneralize #[e])
        g.withContext do
          let elimInfo ← getElimInfo `Quot.ind
          let res ← ElimApp.mkElimApp elimInfo #[e] (← g.getTag)
          let elimArgs := res.elimApp.getAppArgs
          ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! #[e.fvarId!]
          g.assign res.elimApp
          let #[{ name := n, mvarId := g, .. }] := res.alts | unreachable!
          let (v, g) ← g.intro x
          let (varsOut, g) ← g.introNP vars.size
          let fs' := (vars.zip varsOut).foldl (init := fs) fun fs (v, w) => fs.insert v (mkFVar w)
          pure ([(n, ps)], #[⟨⟨g, #[mkFVar v], fs'⟩, n⟩])
      | ConstantInfo.inductInfo info, _ => do
        let (altVarNames, r) ← processConstructors pat.ref info.numParams #[] info.ctors pat.asAlts
        (r, ·) <$> g.cases e.fvarId! altVarNames (useNatCasesAuxOn := true)
      | _, _ => failK ()
    (·.2) <$> subgoals.foldlM (init := (r, a)) fun (r, a) ⟨goal, ctorName⟩ => do
      let rec
      /-- Runs `rcasesContinue` on the first pattern in `r` with a matching `ctorName`.
      The unprocessed patterns (subsequent to the matching pattern) are returned. -/
      align : ListΠ (Name × ListΠ RCasesPatt) → TermElabM (ListΠ (Name × ListΠ RCasesPatt) × α)
      | [] => pure ([], a)
      | (tgt, ps) :: as => do
        if tgt == ctorName then
          let fs := fs.append goal.subst
          (as, ·) <$> rcasesContinue goal.mvarId fs clears a (ps.zip goal.fields.toList) cont
        else
          align as
      align r

/--
This will match a list of patterns against a list of hypotheses `e`. The arguments are similar
to `rcasesCore`, but the patterns and local variables are in `pats`. Because the calls are all
nested in continuations, later arguments can be matched many times, once per goal produced by
earlier arguments. For example `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the
`a` branch and once on `b`.
-/
partial def rcasesContinue (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (a : α)
  (pats : ListΠ (RCasesPatt × Expr)) (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) :
  TermElabM α :=
  match pats with
  | []  => cont g fs clears a
  | ((pat, e) :: ps) =>
    rcasesCore g fs clears e a pat fun g fs clears a =>
      rcasesContinue g fs clears a ps cont

end

/-- Like `tryClearMany`, but also clears dependent hypotheses if possible -/
def tryClearMany' (goal : MVarId) (fvarIds : Array FVarId) : MetaM MVarId := do
  let mut toErase := fvarIds
  for localDecl in (← goal.getDecl).lctx do
    if ← findLocalDeclDependsOn localDecl toErase.contains then
      toErase := toErase.push localDecl.fvarId
  goal.tryClearMany toErase

/--
The terminating continuation used in `rcasesCore` and `rcasesContinue`. We specialize the type
`α` to `Array MVarId` to collect the list of goals, and given the list of `clears`, it attempts to
clear them from the goal and adds the goal to the list.
-/
def finish (toTag : Array (Ident × FVarId) := #[])
  (g : MVarId) (fs : FVarSubst) (clears : Array FVarId)
  (gs : Array MVarId) : TermElabM (Array MVarId) := do
  let cs : Array Expr := (clears.map fs.get).filter Expr.isFVar
  let g ← tryClearMany' g (cs.map Expr.fvarId!)
  g.withContext do
    for (stx, fvar) in toTag do
      Term.addLocalVarInfo stx (fs.get fvar)
  return gs.push g

open Elab

/-- Parses a `Syntax` into the `RCasesPatt` type used by the `RCases` tactic. -/
partial def RCasesPatt.parse (stx : Syntax) : MetaM RCasesPatt :=
  match stx with
  | `(rcasesPatMed| $ps:rcasesPat|*) => return .alts' stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPatLo| $pat:rcasesPatMed : $t:term) => return .typed stx (← parse pat) t
  | `(rcasesPatLo| $pat:rcasesPatMed) => parse pat
  | `(rcasesPat| _) => return .one stx `_
  | `(rcasesPat| $h:ident) => return .one h h.getId
  | `(rcasesPat| -) => return .clear stx
  | `(rcasesPat| @$pat) => return .explicit stx (← parse pat)
  | `(rcasesPat| ⟨$ps,*⟩) => return .tuple stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPat| ($pat)) => return .paren stx (← parse pat)
  | _ => throwUnsupportedSyntax

-- extracted from elabCasesTargets
/-- Generalize all the arguments as specified in `args` to fvars if they aren't already -/
def generalizeExceptFVar (goal : MVarId) (args : Array GeneralizeArg) :
    MetaM (Array Expr × Array FVarId × MVarId) := do
  let argsToGeneralize := args.filter fun arg => !(arg.expr.isFVar && arg.hName?.isNone)
  let (fvarIdsNew, goal) ← goal.generalize argsToGeneralize
  let mut result := #[]
  let mut j := 0
  for arg in args do
    if arg.expr.isFVar && arg.hName?.isNone then
      result := result.push arg.expr
    else
      result := result.push (mkFVar fvarIdsNew[j]!)
      j := j+1
  pure (result, fvarIdsNew[j:], goal)

/--
Given a list of targets of the form `e` or `h : e`, and a pattern, match all the targets
against the pattern. Returns the list of produced subgoals.
-/
def rcases (tgts : Array (Option Ident × Syntax))
  (pat : RCasesPatt) (g : MVarId) : TermElabM (List MVarId) := Term.withSynthesize do
  let pats ← match tgts.size with
  | 0 => return [g]
  | 1 => pure [pat]
  | _ => pure (processConstructor pat.ref (tgts.map fun _ => {}) false 0 pat.asTuple.2).2
  let (pats, args) := Array.unzip <|← (tgts.zip pats.toArray).mapM fun ((hName?, tgt), pat) => do
    let (pat, ty) ← match pat with
    | .typed ref pat ty => withRef ref do
      let ty ← Term.elabType ty
      pure (.typed ref pat (← Term.exprToSyntax ty), some ty)
    | _ => pure (pat, none)
    let expr ← Term.ensureHasType ty (← Term.elabTerm tgt ty)
    pure (pat, { expr, xName? := pat.name?, hName? := hName?.map (·.getId) : GeneralizeArg })
  let (vs, hs, g) ← generalizeExceptFVar g args
  let toTag := tgts.filterMap (·.1) |>.zip hs
  let gs ← rcasesContinue g {} #[] #[] (pats.zip vs).toList (finish (toTag := toTag))
  pure gs.toList

/--
The `obtain` tactic in the no-target case. Given a type `T`, create a goal `|- T` and
and pattern match `T` against the given pattern. Returns the list of goals, with the assumed goal
first followed by the goals produced by the pattern match.
-/
def obtainNone (pat : RCasesPatt) (ty : Syntax) (g : MVarId) : TermElabM (List MVarId) :=
  Term.withSynthesize do
    let ty ← Term.elabType ty
    let g₁ ← mkFreshExprMVar (some ty)
    let (v, g₂) ← (← g.assert (pat.name?.getD default) ty g₁).intro1
    let gs ← rcasesCore g₂ {} #[] (.fvar v) #[] pat finish
    pure (g₁.mvarId! :: gs.toList)

mutual
variable [Monad m] [MonadQuotation m]

/-- Expand a `rintroPat` into an equivalent list of `rcasesPat` patterns. -/
partial def expandRIntroPat (pat : TSyntax `rintroPat)
    (acc : Array (TSyntax `rcasesPat) := #[]) (ty? : Option Term := none) :
    Array (TSyntax `rcasesPat) :=
  match pat with
  | `(rintroPat| $p:rcasesPat) => match ty? with
    | some ty => acc.push <| Unhygienic.run <| withRef p `(rcasesPat| ($p:rcasesPat : $ty))
    | none => acc.push p
  | `(rintroPat| ($(pats)* $[: $ty?']?)) => expandRIntroPats pats acc (ty?' <|> ty?)
  | _ => acc

/-- Expand a list of `rintroPat` into an equivalent list of `rcasesPat` patterns. -/
partial def expandRIntroPats (pats : Array (TSyntax `rintroPat))
    (acc : Array (TSyntax `rcasesPat) := #[]) (ty? : Option Term := none) :
    Array (TSyntax `rcasesPat) :=
  pats.foldl (fun acc p => expandRIntroPat p acc ty?) acc

end

mutual

/--
This introduces the pattern `pat`. It has the same arguments as `rcasesCore`, plus:
* `ty?`: the nearest enclosing type ascription on the current pattern
-/
partial def rintroCore (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (a : α)
    (ref : Syntax) (pat : TSyntax `rintroPat) (ty? : Option Term)
    (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) : TermElabM α := do
  match pat with
  | `(rintroPat| $pat:rcasesPat) =>
    let pat := (← RCasesPatt.parse pat).typed? ref ty?
    let (v, g) ← g.intro (pat.name?.getD `_)
    rcasesCore g fs clears (.fvar v) a pat cont
  | `(rintroPat| ($(pats)* $[: $ty?']?)) =>
    let ref := if pats.size == 1 then pat.raw else .missing
    rintroContinue g fs clears ref pats (ty?' <|> ty?) a cont
  | _ => throwUnsupportedSyntax

/--
This introduces the list of patterns `pats`. It has the same arguments as `rcasesCore`, plus:
* `ty?`: the nearest enclosing type ascription on the current pattern
-/
partial def rintroContinue (g : MVarId) (fs : FVarSubst) (clears : Array FVarId)
    (ref : Syntax) (pats : TSyntaxArray `rintroPat) (ty? : Option Term) (a : α)
    (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) : TermElabM α := do
  g.withContext (loop 0 g fs clears a)
where
  /-- Runs `rintroContinue` on `pats[i:]` -/
  loop i g fs clears a := do
    if h : i < pats.size then
      rintroCore g fs clears a ref pats[i] ty? (loop (i+1))
    else cont g fs clears a

end

/--
The implementation of the `rintro` tactic. It takes a list of patterns `pats` and
an optional type ascription `ty?` and introduces the patterns, resulting in zero or more goals.
-/
def rintro (pats : TSyntaxArray `rintroPat) (ty? : Option Term)
    (g : MVarId) : TermElabM (List MVarId) := Term.withSynthesize do
  (·.toList) <$> rintroContinue g {} #[] .missing pats ty? #[] finish

@[builtin_tactic Lean.Parser.Tactic.rcases] def evalRCases : Tactic := fun stx => do
  match stx with
  | `(tactic| rcases%$tk $tgts,* $[with $pat?]?) =>
    let pat ← match pat? with
      | some pat => RCasesPatt.parse pat
      | none     => pure $ RCasesPatt.tuple tk []
    let tgts := tgts.getElems.map fun tgt =>
      (if tgt.raw[0].isNone then none else some ⟨tgt.raw[0][0]⟩, tgt.raw[1])
    let g ← getMainGoal
    g.withContext do replaceMainGoal (← RCases.rcases tgts pat g)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.obtain] def evalObtain : Tactic := fun stx => do
  match stx with
  | `(tactic| obtain%$tk $[$pat?:rcasesPatMed]? $[: $ty?]? $[:= $val?,*]?) =>
    let pat? ← liftM <| pat?.mapM RCasesPatt.parse
    if let some val := val? then
      let pat  := pat?.getD (RCasesPatt.one tk `_)
      let pat  := pat.typed? tk ty?
      let tgts := val.getElems.map fun val => (none, val.raw)
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.rcases tgts pat g)
    else if let some ty := ty? then
      let pat := pat?.getD (RCasesPatt.one tk `this)
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.obtainNone pat ty g)
    else
      throwError "\
        `obtain` requires either an expected type or a value.\n\
        usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.rintro] def evalRIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| rintro $pats* $[: $ty?]?) =>
    let g ← getMainGoal
    g.withContext do replaceMainGoal (← RCases.rintro pats ty? g)
  | _ => throwUnsupportedSyntax

end RCases
