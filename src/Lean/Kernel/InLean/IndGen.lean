/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.CheckerC
public import Lean.Kernel.InLean.Push

/-!
# InLean: the inductive generator (unverified)

Inductives are checked by con-leche's installer, not by Lean's algorithm;
Lean code mimicking the official kernel *generates* the constants as an
unverified step before it.  From a raw `Declaration.inductDecl` this file produces
the block's constants exactly as the official kernel does — the
`InductiveVal`s (`numNested`, `isRec`, `isReflexive` included), the
`ConstructorVal`s and the `RecursorVal`s, nested blocks' auxiliary
recursors `rec_1`, `rec_2`, … included, binder names and infos included
(the elaborator reads a recursor's binder names).  It checks nothing
beyond what generation needs to proceed; a declaration it cannot generate
is an error, never an acceptance.  The checks are con-leche's
(`Lean.Kernel.InLean.Inductives.*`), on these constants.

It is a port of `src/kernel/inductive.cpp` (v4.35.0) with every validity
check removed: `elim_nested_inductive_fn`, the generating half of
`add_inductive_fn` (the telescopes, `is_rec`/`is_reflexive`, the
elimination level, K, `mk_rec_infos`, `declare_recursors`,
`infer_implicit`) and the translation back (`mk_aux_rec_name_map`,
`restore_nested`, `restore_constructor_name`).  The whnf and inference it
needs (telescopes, recursive fields, the elimination level's field sorts)
run on InLean's core.

**The local context.**  The generator's locals are the core's interned
free variables, each declared at its own depth (`St.gdepth`, the number
of locals declared so far, so `(depth, type)` never coincides for two
generator locals), with its binder name and info recorded beside it
(`St.fvNames`) for `mkPi`/`mkLambda`.  The core runs at the current
`gdepth`, so every generator local is in scope.  The nested-elimination
pass needs no type checker; its locals are plain `FVarId`s the core never
sees, kept in a small local context of their own (`PCtx`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace Ind

/-! ## The generator's monad -/

/-- The generator's context: the environment it reads (which grows as it
adds the block's constants) and the declaration's safety and policy. -/
structure Ctx where
  env : Kernel.Environment
  safety : DefinitionSafety := .safe
  coreAxioms : Bool := false
  limits : Limits := {}

/-- The context's environment for the core. -/
def Ctx.fe (c : Ctx) : FEnv :=
  { env := c.env, safety := c.safety, coreAxioms := c.coreAxioms, limits := c.limits }

/-- The generator's local context: its depth (one local per depth), each
local's binder name and info, and a counter for fresh names. -/
structure IState where
  gdepth : Nat := 0
  fvNames : Std.HashMap Nat (Name × BinderInfo) := {}
  nestCtr : Nat := 0

/-- The generator's monad: the core's `CheckCM` under the context, with the
local context. -/
abbrev M := ReaderT Ctx (StateT IState CheckCM)

@[inline] def throwInvalid (msg : String) : M α := throw (.invalid msg)
@[inline] def throwDeclined (msg : String) : M α := throw (.notImplemented msg)
@[inline] def throwInternal (msg : String) : M α := throw (.internal msg)

/-- Run `x` at the environment `env`, the core's memos flushed (an
environment transition). -/
def withEnv (env : Kernel.Environment) (x : M α) : M α := do
  (flushC : CheckCM Unit)
  withReader (fun c => { c with env }) x

/-- The core's entry points at the context's environment. -/
def infer (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  (opInfer μ (← read).fe d e : CheckCM Expr)
def defeq (μ : CheckMode) (d : Nat) (a b : Expr) : M Bool := do
  (opDefeq μ (← read).fe d a b : CheckCM Bool)
def whnf (μ : CheckMode) (d : Nat) (e : Expr) : M Expr := do
  (opWhnf μ (← read).fe d e : CheckCM Expr)
def ensureSort (μ : CheckMode) (d : Nat) (e : Expr) : M Level := do
  (opSort μ (← read).fe d e : CheckCM Level)

/-- The interned free variable at depth `d` of type `ty`. -/
def mkFVar (d : Nat) (ty : Expr) : M Expr := (mkFVarM d ty : CheckCM Expr)

/-- An interned free variable's type and depth. -/
def fvarInfo? (id : FVarId) : M (Option (Expr × Nat)) := do
  match fvParts? id with
  | some (d, _) =>
    match ← (fvarTypeM? id : CheckCM (Option Expr)) with
    | some ty => return some (ty, d)
    | none => return none
  | none => return none

/-- Level equivalence (an exhausted comparison declines, `liftFueled`). -/
def isEquivL (l r : Level) : M Bool := do
  let o ← (isEquivLM l r : CheckCM (Option Bool))
  (liftFueled "level comparison" o : CheckCM Bool)

/-- Pointwise `isEquivL`. -/
def isEquivListL (ls rs : List Level) : M Bool := do
  let o ← (isEquivListLM ls rs : CheckCM (Option Bool))
  (liftFueled "level comparison" o : CheckCM Bool)

/-- A constant's check (`checkConstantValC`), at the context. -/
def checkConstantVal (μ : CheckMode) (n : Name) (lps : List Name) (ty : Expr) : M Unit := do
  (checkConstantValC μ (← read).fe { name := n, levelParams := lps, type := ty } : CheckCM Unit)

/-- A term's syntactic gates (`checkTermWF`). -/
def checkExprWF (pre : String) (n : Name) (lps : List Name) (e : Expr) : M Unit := do
  (checkTermWF (← read).fe pre n lps e : CheckCM Unit)

/-- The level-instantiated type of a stored constant (`constTyAtM`). -/
def constTyAt (ci : ConstantInfo) (us : List Level) : M Expr := do
  (constTyAtM (← read).fe ci.name us : CheckCM Expr)

/-! ## Names (the C++ `name::append_after`) -/

/-- C++ `name::append_after(char const *)`: append to the base name, a
hygienic name's macro scopes kept after it (`a._@…_hyg.0` ↦
`a_ih._@…_hyg.0`, as the official recursors' binder names show) —
Lean's `Name.appendAfter`. -/
def appendAfter (n : Name) (x : String) : Name := n.appendAfter x

/-- C++ `name::append_after(unsigned)`: `n_i` (Lean's
`Name.appendIndexAfter`). -/
def appendIdx (n : Name) (i : Nat) : Name := n.appendIndexAfter i

/-- C++ `mk_rec_name`. -/
def mkRecName (I : Name) : Name := .str I "rec"

/-- Suffix a decline or an internal error raised by `x` with the installer
stage that raised it (a reject's message is the official kernel's). -/
def withStage (stage : String) (x : M α) : M α :=
  tryCatch x fun
    | .invalid m => throw (.invalid m)
    | .notImplemented m => throw (.notImplemented s!"{m} [{stage}]")
    | .internal m => throw (.internal s!"{m} [{stage}]")
    | .limit l => throw (.limit l)

/-! ## The generator's local context -/

/-- Drop every memo that reads constants' types or values: needed where
an environment does not extend the previous one (the restored environment
of a nested block gives the block's constructors other types than the
auxiliary one did).  The free-variable table stays. -/
def flushAllMemos : M Unit := (flushC : CheckCM Unit)

/-- C++ `mk_local_decl`: a new local at the next depth, its type's
annotations consumed. -/
def mkLocal (n : Name) (ty : Expr) (bi : BinderInfo := .default) : M Expr := do
  let d := (← get).gdepth
  let fv ← mkFVar d ty.consumeTypeAnnotations
  modify fun s => { s with gdepth := s.gdepth + 1 }
  if let .fvar id := fv then
    if let some (_, k) := fvParts? id then
      modify fun s =>
        let m := s.fvNames
        let s := { s with fvNames := {} }
        { s with fvNames := m.insert k (n, bi) }
  return fv

/-- C++ `mk_local_decl_for`: a local for a ∀'s binder. -/
def mkLocalFor (t : Expr) : M Expr :=
  match t with
  | .forallE n d _ bi => mkLocal n d bi
  | _ => throwInternal "inductive: mk_local_decl_for on a non-∀"

/-- A local's declaration: name, info, type. -/
def localDecl (fv : Expr) : M (Name × BinderInfo × Expr) := do
  match fv with
  | .fvar id =>
    match fvParts? id with
    | some (_, k) =>
      let (n, bi) := (← get).fvNames.getD k (`a, .default)
      match ← (fvarTypeM? id : CheckCM (Option Expr)) with
      | some ty => return (n, bi, ty)
      | none => throwInternal "inductive: unknown local"
    | none => throwInternal "inductive: foreign local"
  | _ => throwInternal "inductive: not a local"

def localType (fv : Expr) : M Expr := do return (← localDecl fv).2.2

/-- C++ `local_ctx::mk_binding`. -/
def mkBinding (lam : Bool) (xs : Array Expr) (e : Expr) : M Expr := do
  let mut r := e.abstractI xs
  let mut i := xs.size
  while i > 0 do
    i := i - 1
    let (n, bi, ty) ← localDecl xs[i]!
    let tyA := ty.abstractRangeI i xs
    r := if lam then .lam n tyA r bi else .forallE n tyA r bi
  return r

def mkPi (xs : Array Expr) (e : Expr) : M Expr := mkBinding false xs e
def mkLambda (xs : Array Expr) (e : Expr) : M Expr := mkBinding true xs e

/-! ## The core at the generator's depth -/

def gWhnf (μ : CheckMode) (e : Expr) : M Expr := do whnf μ (← get).gdepth e
def gInfer (μ : CheckMode) (e : Expr) : M Expr := do infer μ (← get).gdepth e
def gDefeq (μ : CheckMode) (a b : Expr) : M Bool := do defeq μ (← get).gdepth a b
def gEnsureSort (μ : CheckMode) (e : Expr) : M Level := do ensureSort μ (← get).gdepth e
def gEnsureType (μ : CheckMode) (e : Expr) : M Level := do gEnsureSort μ (← gInfer μ e)

/-- C++ `is_not_zero` (con-leche's `Level.isNeverZero`). -/
def isNeverZero : Level → Bool
  | .zero | .param _ | .mvar _ => false
  | .succ _ => true
  | .max l r => isNeverZero l || isNeverZero r
  | .imax _ r => isNeverZero r

/-- C++ `has_loose_bvars_in_domain`. -/
def hasLooseBVarsInDomain : Expr → Nat → Bool → Bool
  | .forallE _ d b bi, vidx, strict =>
    (d.hasLooseBVarI vidx &&
      (bi == .default || hasLooseBVarsInDomain b 0 strict)) ||
    hasLooseBVarsInDomain b (vidx + 1) strict
  | b, vidx, strict => !strict && b.hasLooseBVarI vidx

/-- C++ `infer_implicit(t, strict)`. -/
def inferImplicit : Expr → Bool → Expr
  | .forallE n d b bi, strict =>
    let nb := inferImplicit b strict
    if bi != .default then .forallE n d nb bi
    else if hasLooseBVarsInDomain nb 0 strict then .forallE n d nb .implicit
    else .forallE n d nb bi
  | t, _ => t

/-! ## `add_inductive_fn` -/

/-- An inductive type of a declaration: name, type, constructors. -/
structure IT where
  name : Name
  type : Expr
  ctors : Array (Name × Expr)
  deriving Inhabited

/-- C++ `rec_info`. -/
structure RecInfo where
  C : Expr
  minors : Array Expr := #[]
  indices : Array Expr := #[]
  major : Expr
  deriving Inhabited

/-- The fixed data of one `add_inductive_fn` run. -/
structure AI where
  μ : CheckMode
  lps : List Name
  levels : List Level
  nparams : Nat
  types : Array IT
  isUnsafe : Bool
  nnested : Nat
  params : Array Expr
  nindices : Array Nat
  resultLevel : Level
  indConsts : Array Expr

def AI.indNames (a : AI) : List Name := (a.types.map (·.name)).toList

def AI.isIndOcc (a : AI) (e : Expr) : Bool :=
  match e with
  | .const n _ => a.types.any (·.name == n)
  | _ => false

def AI.hasIndOcc (a : AI) (t : Expr) : Bool := (t.findI? a.isIndOcc).isSome

/-- C++ `is_rec` (`reflexive = false`: some binder domain of the
syntactic ∀ telescope mentions a type being declared) and `is_reflexive`
(`true`: such a domain that is itself a ∀).  Instantiating the binders,
as `is_reflexive` does, changes neither test. -/
def AI.domsHaveIndOcc (a : AI) (reflexive : Bool) : Expr → Bool
  | .forallE _ d b _ => ((!reflexive || d.isForall) && a.hasIndOcc d) || a.domsHaveIndOcc reflexive b
  | _ => false

/-- C++ `is_valid_ind_app(t, i)`. -/
def AI.isValidIndAppAt (a : AI) (t : Expr) (i : Nat) : Bool :=
  let args := t.getAppArgs
  t.getAppFn == a.indConsts[i]! && args.size == a.nparams + a.nindices[i]! &&
    (List.range a.nparams).all (fun j => a.params[j]! == args[j]!) &&
    (List.range (args.size - a.nparams)).all (fun j => !a.hasIndOcc args[a.nparams + j]!)

/-- C++ `is_valid_ind_app(t)`. -/
def AI.isValidIndApp (a : AI) (t : Expr) : Option Nat :=
  (List.range a.types.size).find? (a.isValidIndAppAt t)

/-- C++ `is_rec_argument`. -/
partial def AI.isRecArgument (a : AI) (t : Expr) : M (Option Nat) := do
  let mut t ← gWhnf a.μ t
  while t.isForall do
    let l ← mkLocalFor t
    t ← gWhnf a.μ (t.bindingBody!.inst1I l)
  return a.isValidIndApp t

/-- C++ `get_I_indices`. -/
def AI.getIIndices (a : AI) (t : Expr) : M (Nat × Array Expr) := do
  match a.isValidIndApp t with
  | some i => return (i, t.getAppArgs.extract a.nparams)
  | none => throwInternal "inductive: get_I_indices on a non-inductive application"

/-- C++ `get_I_indices` on a constructor's result type: a constructor whose
type does not end in a valid application of a type being declared is
rejected as `check_constructors` does. -/
def AI.ctorResultIndices (a : AI) (cn : Name) (t : Expr) : M (Nat × Array Expr) := do
  match a.isValidIndApp t with
  | some i => return (i, t.getAppArgs.extract a.nparams)
  | none => throwInvalid s!"invalid return type for '{cn}'"

/-- The fields of a constructor type, params instantiated (`b_u`), and the
recursive ones (`u`), at fresh locals. -/
def AI.ctorFields (a : AI) (t0 : Expr) : M (Array Expr × Array Expr × Expr) := do
  let mut t := t0
  let mut i := 0
  let mut bu : Array Expr := #[]
  let mut u : Array Expr := #[]
  while t.isForall do
    if i < a.nparams then
      t := t.bindingBody!.inst1I a.params[i]!
    else
      let l ← mkLocalFor t
      bu := bu.push l
      if (← a.isRecArgument t.bindingDomain!).isSome then u := u.push l
      t := t.bindingBody!.inst1I l
    i := i + 1
  return (bu, u, t)

/-- A recursive field's telescope (`xs`) and the inductive application it
ends in. -/
partial def AI.recFieldTele (a : AI) (ui : Expr) : M (Array Expr × Expr) := do
  let mut ty ← gWhnf a.μ (← gInfer a.μ ui)
  let mut xs : Array Expr := #[]
  while ty.isForall do
    let x ← mkLocalFor ty
    xs := xs.push x
    ty ← gWhnf a.μ (ty.bindingBody!.inst1I x)
  return (xs, ty)

/-- The constants one `add_inductive_fn` run produces, in the official
order (types, constructors, recursors), and its environment. -/
structure AIOut where
  inds : Array InductiveVal
  ctors : Array ConstructorVal
  recs : Array RecursorVal
  env : Kernel.Environment

/-- C++ `add_inductive_fn::operator()`. -/
def addInductiveFn (μ : CheckMode)
    (env0 : Kernel.Environment) (lps : List Name) (nparams : Nat) (types : Array IT)
    (isUnsafe : Bool) (nnested : Nat) : M AIOut := do
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  withReader (fun c => { c with safety }) do
  unless namesNodup lps do
    throwInvalid s!"failed to add declaration to environment, duplicate universe level parameter"
  let levels := lps.map Level.param
  -- `check_inductive_types`
  let mut env := env0
  let mut params : Array Expr := #[]
  let mut nindices : Array Nat := #[]
  let mut resultLevel : Level := .zero
  let mut isNotZero := false
  let mut indConsts : Array Expr := #[]
  let mut first := true
  for it in types do
    let mut nidx := 0
    let mut i := 0
    let mut ty ← withEnv env (gWhnf μ it.type)
    while ty.isForall do
      if i < nparams then
        if first then
          let p ← mkLocalFor ty
          params := params.push p
          ty := ty.bindingBody!.inst1I p
        else
          ty := ty.bindingBody!.inst1I params[i]!
        i := i + 1
      else
        let l ← mkLocalFor ty
        ty := ty.bindingBody!.inst1I l
        nidx := nidx + 1
      ty ← withEnv env (gWhnf μ ty)
    if i != nparams then
      throwInvalid "number of parameters mismatch in inductive datatype declaration"
    let s ← withEnv env (gEnsureSort μ ty)
    if first then
      resultLevel := s
      isNotZero := isNeverZero s
    nindices := nindices.push nidx
    indConsts := indConsts.push (.const it.name levels)
    first := false
  let a : AI :=
    { μ := μ, lps := lps, levels := levels, nparams := nparams, types := types
      isUnsafe := isUnsafe, nnested := nnested, params := params, nindices := nindices
      resultLevel := resultLevel, indConsts := indConsts }
  -- `declare_inductive_types`: `is_rec`, `is_reflexive` are syntactic
  let isRec := types.any fun it => it.ctors.any fun (_, t) => a.domsHaveIndOcc false t
  let isReflexive := types.any fun it => it.ctors.any fun (_, t) => a.domsHaveIndOcc true t
  let all := a.indNames
  let mut inds : Array InductiveVal := #[]
  for h : idx in [0:types.size] do
    let it := types[idx]
    let v : InductiveVal :=
      { name := it.name, levelParams := lps, type := it.type
        numParams := nparams, numIndices := nindices[idx]!, all := all
        ctors := (it.ctors.map (·.1)).toList, numNested := nnested, isRec := isRec
        isUnsafe := isUnsafe, isReflexive := isReflexive }
    inds := inds.push v
    env := addConst env (.inductInfo v)
  -- `declare_constructors`
  let mut ctors : Array ConstructorVal := #[]
  for it in types do
    let mut cidx := 0
    for (n, t) in it.ctors do
      let rec arity : Expr → Nat
        | .forallE _ _ b _ => arity b + 1
        | _ => 0
      let v : ConstructorVal :=
        { name := n, levelParams := lps, type := t, induct := it.name
          cidx := cidx, numParams := nparams, numFields := arity t - nparams, isUnsafe := isUnsafe }
      ctors := ctors.push v
      env := addConst env (.ctorInfo v)
      cidx := cidx + 1
  -- `init_elim_level` (`elim_only_at_universe_zero`)
  let elimZero ← withEnv env do
    if isNotZero then pure false
    else if types.size > 1 then pure true
    else match types[0]!.ctors.size with
      | 0 => pure false
      | 1 =>
        let mut ty := types[0]!.ctors[0]!.2
        let mut i := 0
        let mut toCheck : Array Expr := #[]
        while ty.isForall do
          let fv ← mkLocalFor ty
          if i ≥ nparams then
            let s ← gEnsureType μ ty.bindingDomain!
            unless Lvl.isZero s do toCheck := toCheck.push fv
          ty := ty.bindingBody!.inst1I fv
          i := i + 1
        let resArgs := ty.getAppArgs
        pure (toCheck.any fun x => !resArgs.contains x)
      | _ => pure true
  let elimLevel : Level ←
    if elimZero then pure .zero
    else
      let mut u : Name := `u
      let mut i := 1
      while lps.contains u do
        u := appendIdx `u i
        i := i + 1
      pure (.param u)
  -- `init_K_target`
  let kTarget := types.size == 1 && Lvl.isZero resultLevel && types[0]!.ctors.size == 1 &&
    (peelPis nparams types[0]!.ctors[0]!.2).any (!·.isForall)
  let recLevels := match elimLevel with
    | .param _ => elimLevel :: levels
    | _ => levels
  let recLps := match elimLevel with
    | .param u => u :: lps
    | _ => lps
  -- `mk_rec_infos`
  let (Cs, minors, infos) ← withEnv env do
    let mut infos : Array RecInfo := #[]
    for h : dIdx in [0:types.size] do
      let it := types[dIdx]
      let mut t ← gWhnf μ it.type
      let mut i := 0
      let mut indices : Array Expr := #[]
      while t.isForall do
        if i < nparams then
          t := t.bindingBody!.inst1I params[i]!
        else
          let idx ← mkLocalFor t
          indices := indices.push idx
          t := t.bindingBody!.inst1I idx
        i := i + 1
        t ← gWhnf μ t
      let major ← mkLocal `t (mkAppN (mkAppN indConsts[dIdx]! params) indices)
      let cTy ← mkPi indices (← mkPi #[major] (.sort elimLevel))
      let cName : Name := if types.size > 1 then appendIdx `motive (dIdx + 1) else `motive
      let C ← mkLocal cName cTy
      infos := infos.push { C, indices, major }
    for h : dIdx in [0:types.size] do
      let it := types[dIdx]
      for (cn, ct) in it.ctors do
        let (bu, u, t) ← a.ctorFields ct
        let (itIdx, itIndices) ← a.ctorResultIndices cn t
        let introApp := mkAppN (mkAppN (.const cn levels) params) bu
        let cApp := mkApp (mkAppN infos[itIdx]!.C itIndices) introApp
        let mut v : Array Expr := #[]
        for ui in u do
          let (xs, uty) ← a.recFieldTele ui
          let (j, idxs) ← a.getIIndices uty
          let cApp' := mkApp (mkAppN infos[j]!.C idxs) (mkAppN ui xs)
          let viTy ← mkPi xs cApp'
          let (uName, _, _) ← localDecl ui
          v := v.push (← mkLocal (appendAfter uName "_ih") viTy)
        let minorTy ← mkPi bu (← mkPi v cApp)
        let minor ← mkLocal (cn.replacePrefix it.name .anonymous) minorTy
        infos := infos.modify dIdx fun ri => { ri with minors := ri.minors.push minor }
    let Cs := infos.map (·.C)
    let minors := infos.foldl (fun acc ri => acc ++ ri.minors) #[]
    pure (Cs, minors, infos)
  -- `declare_recursors`
  let mut recs : Array RecursorVal := #[]
  let mut minorIdx := 0
  for h : dIdx in [0:types.size] do
    let it := types[dIdx]
    let info := infos[dIdx]!
    let (recTy, rules, mIdx) : Expr × Array RecursorRule × Nat ← withEnv env do
      let cApp := mkApp (mkAppN info.C info.indices) info.major
      let t₁ ← mkPi #[info.major] cApp
      let t₂ ← mkPi info.indices t₁
      let t₃ ← mkPi minors t₂
      let t₄ ← mkPi Cs t₃
      let t₅ ← mkPi params t₄
      let recTy := inferImplicit t₅ true
      -- `mk_rec_rules`
      let mut rules : Array RecursorRule := #[]
      let mut mIdx := minorIdx
      for (cn, ct) in it.ctors do
        let (bu, u, _) ← a.ctorFields ct
        let mut v : Array Expr := #[]
        for ui in u do
          let (xs, uty) ← a.recFieldTele ui
          let (j, idxs) ← a.getIIndices uty
          let recApp := mkApp (mkAppN (mkAppN (mkAppN (mkAppN
            (.const (mkRecName types[j]!.name) recLevels) params) Cs) minors) idxs) (mkAppN ui xs)
          v := v.push (← mkLambda xs recApp)
        let eApp := mkAppN (mkAppN minors[mIdx]! bu) v
        let rhs ← mkLambda params (← mkLambda Cs (← mkLambda minors (← mkLambda bu eApp)))
        rules := rules.push { ctor := cn, nfields := bu.size, rhs }
        mIdx := mIdx + 1
      pure (recTy, rules, mIdx)
    minorIdx := mIdx
    let recName := mkRecName it.name
    let v : RecursorVal :=
      { name := recName, levelParams := recLps, type := recTy, all := all
        numParams := nparams, numIndices := nindices[dIdx]!, numMotives := Cs.size
        numMinors := minors.size, rules := rules.toList, k := kTarget, isUnsafe := isUnsafe }
    recs := recs.push v
    env := addConst env (.recInfo v)
  return { inds, ctors, recs, env }

/-! ## `elim_nested_inductive_fn` and `restore_nested` -/

/-- The nested pass's local context: plain locals the core never sees. -/
abbrev PCtx := Std.HashMap FVarId (Name × Expr × BinderInfo)

def freshP : M FVarId :=
  modifyGet fun s => (⟨.num `_inlean_nest s.nestCtr⟩, { s with nestCtr := s.nestCtr + 1 })

/-- `local_ctx::mk_pi`/`mk_lambda` over a `PCtx`. -/
def pBinding (lctx : PCtx) (lam : Bool) (xs : Array Expr) (e : Expr) : Expr := Id.run do
  let mut r := e.abstractI xs
  let mut i := xs.size
  while i > 0 do
    i := i - 1
    let (n, ty, bi) := lctx.getD xs[i]!.fvarId! (`a, default, .default)
    let tyA := ty.abstractRangeI i xs
    r := if lam then .lam n tyA r bi else .forallE n tyA r bi
  return r

/-- `get_params`: `n` binders opened at plain locals. -/
def getParams (env : Kernel.Environment) (type : Expr) (n : Nat) (lctx : PCtx) :
    M (Expr × Array Expr × PCtx) := do
  let mut type := type
  let mut lctx := lctx
  let mut ps : Array Expr := #[]
  for _ in [0:n] do
    match type with
    | .forallE nm d b bi =>
      let id ← freshP
      lctx := lctx.insert id (nm, d, bi)
      ps := ps.push (.fvar id)
      type := b.inst1I (.fvar id)
    | _ =>
      let _ := env
      throwInvalid "invalid inductive datatype declaration, incorrect number of parameters"
  return (type, ps, lctx)

/-- An exactly-keyed memo key (`Expr.beqI`, decidable equality) (binder names count, as the C++ pointer
cache's results keep them). -/
structure EKey where
  e : Expr

instance : BEq EKey := ⟨fun a b => Expr.beqI a.e b.e⟩
instance : Hashable EKey := ⟨fun k => k.e.hash⟩

/-- The nested pass's state. -/
structure NState where
  newTypes : Array IT
  nestedAux : Array (Expr × Name) := #[]
  nextIdx : Nat := 1

/-- `elim_nested_inductive_fn`. -/
structure Elim where
  env : Kernel.Environment
  lvls : List Level
  nparams : Nat
  params : Array Expr
  paramsLctx : PCtx

abbrev NM := StateT NState M

def Elim.mkUniqueName (el : Elim) (n : Name) : NM Name := do
  repeat
    let i := (← get).nextIdx
    modify fun s => { s with nextIdx := s.nextIdx + 1 }
    let r := appendIdx n i
    if (el.env.find? r).isNone then return r
  return n

/-- `is_nested_inductive_app`. -/
def Elim.isNestedIndApp (el : Elim) (e : Expr) : NM (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let some (.inductInfo iv) := el.env.find? fn | return none
  let args := e.getAppArgs
  if iv.numParams > args.size then return none
  let names := (← get).newTypes.map (·.name)
  let mut isNested := false
  let mut loose := false
  for i in [0:iv.numParams] do
    if args[i]!.hasLooseBVars then loose := true
    if (args[i]!.findI? fun t => match t with
        | .const n _ => names.contains n
        | _ => false).isSome then isNested := true
  if !isNested then return none
  if loose then
    throwInvalid s!"invalid nested inductive datatype '{fn}', nested inductive datatypes \
      parameters cannot contain local variables."
  return some iv

/-- `instantiate_pi_params`. -/
def instantiatePiParams (e : Expr) (n : Nat) (ps : Array Expr) : M Expr := do
  let mut e := e
  for _ in [0:n] do
    match e with
    | .forallE _ _ b _ => e := b
    | _ => throwInvalid "invalid nested inductive datatype, ill-formed declaration"
  return e.instRevRangeI 0 n ps

/-- `replace_if_nested`. -/
def Elim.replaceIfNested (el : Elim) (lctx : PCtx) (As : Array Expr) (e : Expr) :
    NM (Option Expr) := do
  let some iv ← el.isNestedIndApp e | return none
  let args := e.getAppArgs
  let fn := e.getAppFn
  let .const iName iLvls := fn | return none
  let np := iv.numParams
  let iAs := mkAppN fn (args.extract 0 np)
  let iParams := (iAs.abstractI As).instRevI el.params
  if let some (_, auxI) := (← get).nestedAux.find? (Expr.clEq ·.1 iParams) then
    return some (mkAppN (mkAppN (.const auxI el.lvls) As) (args.extract np))
  let mut result : Option Expr := none
  for jName in iv.all do
    let some jInfo := el.env.find? jName | throwInternal "nested: unknown inductive"
    let jAs := mkAppN (.const jName iLvls) (args.extract 0 np)
    let auxJ ← el.mkUniqueName (`_nested ++ jName)
    let auxJType ← instantiatePiParams (jInfo.type.instLvlParamsGenI jInfo.levelParams iLvls)
      np args
    let auxJType := pBinding lctx false As auxJType
    modify fun s => { s with nestedAux := s.nestedAux.push ((jAs.abstractI As).instRevI el.params, auxJ) }
    if jName == iName then
      result := some (mkAppN (mkAppN (.const auxJ el.lvls) As) (args.extract np))
    let some (.inductInfo jv) := some jInfo | throwInternal "nested: not an inductive"
    let mut cs : Array (Name × Expr) := #[]
    for jc in jv.ctors do
      let some jci := el.env.find? jc | throwInternal "nested: unknown constructor"
      let cTy ← instantiatePiParams (jci.type.instLvlParamsGenI jci.levelParams iLvls) np args
      cs := cs.push (jc.replacePrefix jName auxJ, pBinding lctx false As cTy)
    modify fun s => { s with newTypes := s.newTypes.push { name := auxJ, type := auxJType, ctors := cs } }
  return result

/-- `replace_all_nested`: core's `replace` order (the function before the
argument, the domain before the body), its cache keyed by exact equality (`Expr.beqI`). -/
partial def Elim.replaceAllNested (el : Elim) (lctx : PCtx) (As : Array Expr) (e : Expr) :
    NM Expr := do
  let rec go (e : Expr) : StateT (Std.HashMap EKey Expr) NM Expr := do
    if let some r := (← get)[EKey.mk e]? then return r
    let r ← match ← el.replaceIfNested lctx As e with
      | some r => pure r
      | none =>
        match e with
        | .mdata _ b => pure (e.updateMData! (← go b))
        | .proj _ _ b => pure (e.updateProj! (← go b))
        | .app f a => do let f' ← go f; let a' ← go a; pure (e.updateApp! f' a')
        | .forallE _ d b _ => do let d' ← go d; let b' ← go b; pure (e.updateForallE! d' b')
        | .lam _ d b _ => do let d' ← go d; let b' ← go b; pure (e.updateLambdaE! d' b')
        | .letE _ t v b _ => do
          let t' ← go t; let v' ← go v; let b' ← go b; pure (e.updateLetE! t' v' b')
        | _ => pure e
    modify fun m => m.insert (EKey.mk e) r
    return r
  (go e).run' {}

/-- C++ `check_no_nested_aux`: does `e` name a constant, or a projection's
structure, under the reserved prefix `_nested` of the nested pass's
auxiliary types? -/
def usesNestedPrefix (e : Expr) : Bool :=
  (e.findI? fun t => match t with
    | .const n _ => (`_nested).isPrefixOf n
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false).isSome

/-- C++ `check_uniform_ind_occs` on one constructor type: the first
occurrence of a type being declared (one of `names`) that is not applied to
the parameters (the constructor's first `np` binders, as bound variables)
at the declaration's levels `lvls`, if any.  An application to more
arguments is descended into (its indices are checked too); `for_each`'s
cache is the visited set. -/
partial def nonUniformOcc (names : Array Name) (lvls : List Level) (np : Nat) (e : Expr) :
    Option Name :=
  let rec go (e : Expr) (off : Nat) : StateM (Std.HashSet (EKey × Nat)) (Option Name) := do
    if (← get).contains (EKey.mk e, off) then return none
    modify (·.insert (EKey.mk e, off))
    let args := e.getAppArgs
    match e.getAppFn with
    | .const c us =>
      if names.contains c && args.size ≤ np then
        let ok := args.size == np && off ≥ np && us == lvls &&
          (List.range np).all fun i => args[i]! == .bvar (off - 1 - i)
        return if ok then none else some c
    | _ => pure ()
    match e with
    | .app f x => do
      if let some c ← go f off then return some c
      go x off
    | .forallE _ d b _ | .lam _ d b _ => do
      if let some c ← go d off then return some c
      go b (off + 1)
    | .letE _ t v b _ => do
      if let some c ← go t off then return some c
      if let some c ← go v off then return some c
      go b (off + 1)
    | .mdata _ b | .proj _ _ b => go b off
    | _ => return none
  (go e 0).run' {}

/-- The result of the nested pass (`elim_nested_inductive_result`). -/
structure ElimRes where
  params : Array Expr
  paramsLctx : PCtx
  aux2nested : Array (Name × Expr)
  auxTypes : Array IT

/-- `elim_nested_inductive_fn::operator()`. -/
def elimNested (env : Kernel.Environment) (lps : List Name) (nparams : Nat) (types : Array IT) :
    M ElimRes := do
  if types.isEmpty then
    throwInvalid "invalid empty (mutual) inductive datatype declaration, it must contain at least \
      one inductive type."
  let (_, params, plctx) ← getParams env types[0]!.type nparams {}
  let el : Elim := { env, lvls := lps.map Level.param, nparams, params, paramsLctx := plctx }
  let run : NM Unit := do
    let mut qhead := 0
    while qhead < (← get).newTypes.size do
      let it := (← get).newTypes[qhead]!
      let mut newCs : Array (Name × Expr) := #[]
      for (cn, ct) in it.ctors do
        let (ct', As, lctx) ← getParams env ct nparams {}
        let nct ← el.replaceAllNested lctx As ct'
        newCs := newCs.push (cn, pBinding lctx false As nct)
      modify fun s => { s with newTypes := s.newTypes.set! qhead { it with ctors := newCs } }
      qhead := qhead + 1
  let ((), st) ← run.run { newTypes := types }
  return { params, paramsLctx := plctx, aux2nested := st.nestedAux.map fun (e, n) => (n, e),
           auxTypes := st.newTypes }

/-- `get_nested_if_aux_constructor`. -/
def ElimRes.nestedIfAuxCtor (r : ElimRes) (auxEnv : Kernel.Environment) (c : Name) :
    Option (Expr × Name) :=
  match auxEnv.find? c with
  | some (.ctorInfo cv) =>
    match r.aux2nested.find? (·.1 == cv.induct) with
    | some (_, nested) => some (nested, cv.induct)
    | none => none
  | _ => none

/-- `restore_constructor_name`. -/
def ElimRes.restoreCtorName (r : ElimRes) (auxEnv : Kernel.Environment) (c : Name) : M Name := do
  match r.nestedIfAuxCtor auxEnv c with
  | some (nested, auxI) =>
    match nested.getAppFn with
    | .const I _ => return c.replacePrefix auxI I
    | _ => throwInvalid "failed to restore nested inductive types, nested occurrence is not an \
        inductive type application"
  | none => throwInvalid s!"failed to restore nested inductive types, '{c}' is not a constructor \
      of an auxiliary type"

/-- `restore_nested`. -/
def ElimRes.restoreNested (r : ElimRes) (auxEnv : Kernel.Environment) (e : Expr)
    (recMap : Array (Name × Name) := #[]) : M Expr := do
  let mut e := e
  let mut lctx : PCtx := {}
  let mut As : Array Expr := #[]
  let pi := e.isForall
  for _ in [0:r.params.size] do
    match e with
    | .forallE n d b bi | .lam n d b bi =>
      let id ← freshP
      lctx := lctx.insert id (n, d, bi)
      As := As.push (.fvar id)
      e := b.inst1I (.fvar id)
    | _ => throwInvalid "failed to restore nested inductive types, fewer binders than parameters"
  let np := r.params.size
  let As' := As
  let e' := e.replaceI fun t =>
    let fromRec : Option Expr := match t with
      | .const n us => (recMap.find? (·.1 == n)).map fun (_, m) => .const m us
      | _ => none
    if fromRec.isSome then fromRec else
    match t.getAppFn with
    | .const fn _ =>
      match r.aux2nested.find? (·.1 == fn) with
      | some (_, nested) =>
        let args := t.getAppArgs
        if args.size < np then none else
        let newT := (nested.abstractI r.params).instRevI As'
        some (mkAppN newT (args.extract np))
      | none =>
        match r.nestedIfAuxCtor auxEnv fn with
        | some (nested, auxI) =>
          let args := t.getAppArgs
          if args.size < np then none else
          let newNested := (nested.abstractI r.params).instRevI As'
          match newNested.getAppFn with
          | .const I iLvls =>
            some (mkAppN (mkAppN (.const (fn.replacePrefix auxI I) iLvls) newNested.getAppArgs)
              (args.extract np))
          | _ => none
        | none => none
    | _ => none
  return pBinding lctx (!pi) As e'

/-- **`environment::add_inductive`'s output**: the constants a raw
inductive declaration adds, in the official order — generated, not
checked. -/
def genInductive (μ : CheckMode)
    (lps : List Name) (nparams : Nat) (types0 : List InductiveType) (isUnsafe : Bool) :
    M Added := do
  let env ← read <&> (·.env)
  let types : Array IT := types0.toArray.map fun it =>
    { name := it.name, type := it.type, ctors := (it.ctors.map fun c => (c.name, c.type)).toArray }
  -- `add_inductive`'s checks before generation: no metavariable, free
  -- variable or reserved auxiliary name (`check_no_metavar_no_fvar`,
  -- `check_no_nested_aux`), the types being declared applied uniformly
  -- (`check_uniform_ind_occs`)
  for it in types do
    for (n, e) in #[(it.name, it.type)] ++ it.ctors do
      if e.hasMVar then throwInvalid s!"declaration has metavariables '{n}'"
      if e.hasFVar then throwInvalid s!"declaration has free variables '{n}'"
      if usesNestedPrefix e then
        throwInvalid s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"
  let names := types.map (·.name)
  let lvls := lps.map Level.param
  for it in types do
    for (_, ct) in it.ctors do
      if let some c := nonUniformOcc names lvls nparams ct then
        throwInvalid s!"invalid occurrence of datatype '{c}' being declared: it must be applied \
          to the parameters and universe levels of the mutual declaration"
  let res ← elimNested env lps nparams types
  let nnested := res.aux2nested.size
  let out ← withStage "inductive generator" <|
    addInductiveFn μ env lps nparams res.auxTypes isUnsafe nnested
  let consts : Array ConstantInfo ← if nnested == 0 then
      pure ((out.inds.map .inductInfo) ++ (out.ctors.map .ctorInfo) ++ (out.recs.map .recInfo))
    else do
      -- restore the nested inductives
      let allNames := (types.map (·.name)).toList
      let main := types[0]!.name
      let auxAll := (out.inds.find? (·.name == main)).map (·.all) |>.getD []
      let mut recMap : Array (Name × Name) := #[]
      let mut auxRecs : Array Name := #[]
      let mut nextIdx := 1
      for (n, i) in auxAll.zipIdx do
        if i ≥ types.size then
          auxRecs := auxRecs.push (mkRecName n)
          recMap := recMap.push (mkRecName n, appendIdx (mkRecName main) nextIdx)
          nextIdx := nextIdx + 1
      let mut cs : Array ConstantInfo := #[]
      let processRec (recName : Name) : M ConstantInfo := do
        let newName := ((recMap.find? (·.1 == recName)).map (·.2)).getD recName
        let some (.recInfo rv) := out.env.find? recName | throwInternal "nested: recursor missing"
        let newTy ← res.restoreNested out.env rv.type recMap
        let mut rules : Array RecursorRule := #[]
        for rl in rv.rules do
          let rhs ← res.restoreNested out.env rl.rhs recMap
          let cn ← if newName != recName then res.restoreCtorName out.env rl.ctor else pure rl.ctor
          rules := rules.push { ctor := cn, nfields := rl.nfields, rhs }
        return .recInfo { rv with name := newName, type := newTy, all := allNames,
                                  rules := rules.toList }
      for it in types do
        let some (.inductInfo iv) := out.env.find? it.name | throwInternal "nested: type missing"
        cs := cs.push (.inductInfo { iv with all := allNames })
        for cn in iv.ctors do
          let some (.ctorInfo cv) := out.env.find? cn | throwInternal "nested: constructor missing"
          cs := cs.push (.ctorInfo { cv with type := ← res.restoreNested out.env cv.type })
        cs := cs.push (← processRec (mkRecName it.name))
      for r in auxRecs do
        cs := cs.push (← processRec r)
      pure cs
  return { consts }

end Ind

end Lean.Kernel.InLean
