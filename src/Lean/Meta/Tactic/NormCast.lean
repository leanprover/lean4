/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Attr
public import Lean.Meta.CoeAttr

public section

namespace Lean.Meta.NormCast
/--
`Label` is a type used to classify `norm_cast` lemmas.
* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
inductive Label
  /-- elim lemma: LHS has 0 head coes and ≥ 1 internal coe -/
  | elim
  /-- move lemma: LHS has 1 head coe and 0 internal coes,
  RHS has 0 head coes and ≥ 1 internal coes -/
  | move
  /-- squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes -/
  | squash
  deriving DecidableEq, Repr, Inhabited

/-- Assuming `e` is an application, returns the list of subterms that `simp` will rewrite in. -/
def getSimpArgs (e : Expr) : MetaM (Array Expr) := do
  match ← mkCongrSimp? e.getAppFn with
  | none => return e.getAppArgs
  | some {argKinds, ..} =>
    let mut args := #[]
    for a in e.getAppArgs, k in argKinds do
      if k matches .eq then
        args := args.push a
    return args

/-- Counts how many coercions are at the head of the expression. -/
partial def countHeadCoes (e : Expr) : MetaM Nat := do
  if let Expr.const fn .. := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs >= info.numArgs then
        return (← countHeadCoes (e.getArg! info.coercee)) + 1
  return 0

/-- Counts how many coercions are inside the expression, including the head ones. -/
partial def countCoes (e : Expr) : MetaM Nat :=
  lambdaTelescope e fun _ e => do
    if let Expr.const fn .. := e.getAppFn then
      if let some info ← getCoeFnInfo? fn then
        if e.getAppNumArgs >= info.numArgs then
          let mut coes := (← countHeadCoes (e.getArg! info.coercee)) + 1
          for i in info.numArgs...e.getAppNumArgs do
            coes := coes + (← countCoes (e.getArg! i))
          return coes
    return (← (← getSimpArgs e).mapM countCoes).foldl (·+·) 0

/-- Counts how many coercions are inside the expression, excluding the head ones. -/
def countInternalCoes (e : Expr) : MetaM Nat :=
  return (← countCoes e) - (← countHeadCoes e)

/-- Classifies a declaration of type `ty` as a `norm_cast` rule. -/
def classifyType (ty : Expr) : MetaM Label :=
  forallTelescopeReducing ty fun _ ty => do
    let ty ← whnf ty
    let (lhs, rhs) ←
      if ty.isAppOfArity ``Eq 3 then pure (ty.getArg! 1, ty.getArg! 2)
      else if ty.isAppOfArity ``Iff 2 then pure (ty.getArg! 0, ty.getArg! 1)
      else throwError "Invalid `norm_cast` lemma: Expected an equality or iff, but found{indentExpr ty}"
    let lhsCoes ← countCoes lhs
    let coeFnNote := MessageData.note m!"coe functions are registered using the `[coe]` attribute"
    if lhsCoes = 0 then
      throwError m!"Invalid `norm_cast` lemma: At least one coe function must appear in the left-hand side{indentExpr lhs}" ++ coeFnNote
    let lhsHeadCoes ← countHeadCoes lhs
    let rhsHeadCoes ← countHeadCoes rhs
    let rhsInternalCoes ← countInternalCoes rhs
    if lhsHeadCoes = 0 then
      return Label.elim
    else if lhsHeadCoes = 1 then do
      unless rhsHeadCoes = 0 do
        throwError m!"Invalid `norm_cast` lemma: The right-hand side cannot start with a coe function{indentExpr rhs}" ++ coeFnNote
      if rhsInternalCoes = 0 then
        return Label.squash
      else
        return Label.move
    else if rhsHeadCoes < lhsHeadCoes then do
      return Label.squash
    else do
      throwError m!"\
        Invalid `norm_cast` squash lemma: \
        The right-hand side must have fewer coe functions in head position than the left-hand side{indentExpr ty}" ++ coeFnNote

/-- The `push_cast` simp attribute. -/
builtin_initialize pushCastExt : SimpExtension ←
  registerSimpAttr `push_cast "\
    The `push_cast` simp attribute uses `norm_cast` lemmas \
    to move casts toward the leaf nodes of the expression."

/--  The `norm_cast` attribute stores a simp set for each of the three types of `norm_cast` lemma. -/
structure NormCastExtension where
  /-- A simp set which lifts coercions to the top level. -/
  up : SimpExtension
  /-- A simp set which pushes coercions to the leaves. -/
  down : SimpExtension
  /-- A simp set which simplifies transitive coercions. -/
  squash : SimpExtension
deriving Inhabited

/-- The `norm_cast` extension data. -/
builtin_initialize normCastExt : NormCastExtension ← pure {
  up := ← mkSimpExt (decl_name% ++ `up)
  down := ← mkSimpExt (decl_name% ++ `down)
  squash := ← mkSimpExt (decl_name% ++ `squash)
}

/-- `addElim decl` adds `decl` as an `elim` lemma to be used by `norm_cast`. -/
def addElim (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit :=
  addSimpTheorem normCastExt.up decl (post := true) (inv := false) kind prio

/-- `addMove decl` adds `decl` as a `move` lemma to be used by `norm_cast`. -/
def addMove (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.up decl (post := true) (inv := true) kind prio
  addSimpTheorem normCastExt.down decl (post := true) (inv := false) kind prio

/-- `addSquash decl` adds `decl` as a `squash` lemma to be used by `norm_cast`. -/
def addSquash (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  addSimpTheorem pushCastExt decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.squash decl (post := true) (inv := false) kind prio
  addSimpTheorem normCastExt.down decl (post := true) (inv := false) kind prio

/-- `addInfer decl` infers the label of `decl` (`elim`, `move`, or `squash`) and arranges for it to
be used by `norm_cast`.

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
def addInfer (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM Unit := do
  let ty := (← getConstVal decl).type
  match ← classifyType ty with
  | Label.elim => addElim decl kind prio
  | Label.squash => addSquash decl kind prio
  | Label.move => addMove decl kind prio

builtin_initialize registerBuiltinAttribute {
  name := `norm_cast
  descr := "attribute for norm_cast"
  add := fun decl stx kind => MetaM.run' do
    let `(attr| norm_cast $[$label:normCastLabel]? $[$prio]?) := stx | unreachable!
    let prio := (prio.bind (·.1.isNatLit?)).getD (eval_prio default)
    match label.bind (·.1.isStrLit?) with
    | "elim" => addElim decl kind prio
    | "move" => addMove decl kind prio
    | "squash" => addSquash decl kind prio
    | none => addInfer decl kind prio
    | _ => unreachable!
}

end Lean.Meta.NormCast
