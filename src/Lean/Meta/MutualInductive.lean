/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.NestedInductive
import Lean.Meta.WHNF
import Lean.AddDecl

/-!
# Certificates for mutual inductive declarations

A mutual inductive block is a single inductive family in disguise: the types differ only in which
of them a constructor returns, and the kernel already insists they share their parameters and their
universe. Generate an enumeration `Idx` with one constructor per type of the block, carrying that
type's indices, and the block becomes one declaration `M : ∀ params, Idx params → Sort u` whose
constructors are the block's.

This module builds that model and presents the block as definitions over it, in the shape
`NestedGen` already established: the type `Tᵢ` is `M params (Idx.mkᵢ params indices)`, its
constructors are the model's, and `Tᵢ.rec` is `M.rec` at a motive that dispatches on the index. The
dispatch is what makes the whole thing work out: a computation rule fires at a constructor, whose
index is a literal `Idx.mkᵢ`, so the dispatch iota-reduces and every rule of the block holds
definitionally over the model. Nothing here has to prove anything, unlike the nested case.

Lean 3 did the same reduction with `PSum` and `PSigma` in place of a generated enumeration, and had
to pad the minor premises with `PUnit` because its recursors took only their own component's. Lean 4
recursors take the whole block's motives and minor premises, in the order the model's own recursor
wants them, so they pass straight through.
-/

namespace Lean.Meta

namespace MutualGen

open NestedGen (RestoredRec)

/-- A mutual inductive block, with its parameters opened. -/
structure Block where
  lparams  : List Name
  nparams  : Nat
  types    : Array InductiveType
  /-- The block's parameters, as local hypotheses; every type of the block shares them. -/
  params   : Array Expr
  /-- How many indices each type of the block takes. -/
  nindices : Array Nat
  /-- The sort every type of the block ends in. -/
  level    : Level

def Block.lvls (b : Block) : List Level := b.lparams.map Level.param

/-- Introduce `decls` as local hypotheses, in order, with default binder annotations. -/
private def withLocals {α : Type} (decls : Array (Name × Expr)) (k : Array Expr → MetaM α) :
    MetaM α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM α :=
    if h : i < decls.size then
      withLocalDeclD decls[i].1 decls[i].2 fun x => go (i + 1) (acc.push x)
    else
      k acc
  termination_by decls.size - i

private def anyDomain (p : Expr → Bool) : Expr → Bool
  | .forallE _ d b _ => p d || anyDomain p b
  | _ => false

private def hasOwnOcc (types : Array InductiveType) (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => types.any (·.name == n)
    | _ => false).isSome

/-- One of the block's types at its own universes, parameters and full complement of indices. -/
def Block.indApp?' (b : Block) (e : Expr) : Option (Nat × Array Expr) := Id.run do
  let .const n us := e.getAppFn | return none
  let some j := b.types.findIdx? (·.name == n) | return none
  if us != b.lvls then return none
  let args := e.getAppArgs
  if args.size != b.nparams + b.nindices[j]! then return none
  for i in [0 : b.nparams] do
    if args[i]! != b.params[i]! then return none
  return some (j, args.extract b.nparams args.size)

/--
Whether `e` is an occurrence of one of the block's types, and if so which one and at which indices.

`is_valid_ind_app` decides the same question, and everything it asks is asked here, the rule that no
index argument may mention a type of the block included: such an occurrence is unsound in general, so
what stands there is not one of these however it is written.
-/
def Block.indApp? (b : Block) (e : Expr) : Option (Nat × Array Expr) := do
  let (j, indices) ← b.indApp?' e
  guard <| !indices.any (hasOwnOcc b.types)
  return (j, indices)

/-- The type of the block at `j`, applied to the block's parameters and to `indices`. -/
def Block.app (b : Block) (j : Nat) (indices : Array Expr) : Expr :=
  mkAppN (mkConst b.types[j]!.name b.lvls) (b.params ++ indices)

/--
The type of the block at `j` with its parameters instantiated, reduced binder by binder as
`check_inductive_types` reduces it: a type is checked before the block exists, so unlike a
constructor's it may need unfolding to expose the next parameter.
-/
def Block.instantiateParams (b : Block) (j : Nat) : MetaM (Option Expr) := do
  let mut ty ← whnf b.types[j]!.type
  for p in b.params do
    let .forallE _ _ body _ := ty | return none
    ty ← whnf (body.instantiate1 p)
  return some ty

/-- The indices of the type of the block at `j`, as local hypotheses. -/
def Block.withIndices {α} (b : Block) (j : Nat) (k : Array Expr → MetaM α) : MetaM α := do
  let some ty ← b.instantiateParams j | throwError "'{b.types[j]!.name}' takes too few parameters"
  forallBoundedTelescope ty b.nindices[j]! (whnfType := true) fun indices _ => k indices

/--
Walk the binders of the type of the constructor field `f`. At the head, `leaf` is handed the
component the field recurses into, the indices it is at and the field applied to those binders; the
binders are then put back, as `∀` if `pi` and as `fun` otherwise. `none` if the field is not
recursive.

A field's type is reduced to find the occurrence, as `is_rec_argument` reduces the model's, but only
as far as the block's own types: past them lie the definitions realising them, whose heads are the
model rather than the block, and the block is what the recursor being derived is stated about.
-/
partial def Block.underField (b : Block) (pi : Bool) (f fty : Expr)
    (leaf : Nat → Array Expr → Expr → Expr) (xs : Array Expr := #[]) : MetaM (Option Expr) := do
  match ← whnfHeadPred fty fun e => return (b.indApp? e).isNone with
  | .forallE n d body bi =>
    withLocalDecl n bi d fun x => do
      let some r ← b.underField pi f (body.instantiate1 x) leaf (xs.push x) | return none
      return some (← if pi then mkForallFVars #[x] r else mkLambdaFVars #[x] r)
  | fty =>
    let some (j, indices) := b.indApp? fty | return none
    return some (leaf j indices (mkAppN f xs))

/-- Whether some constructor takes an argument mentioning a type of the block. -/
def isRecursive (types : Array InductiveType) : Bool :=
  types.any fun t => t.ctors.any fun c => anyDomain (hasOwnOcc types) c.type

/-- Whether some constructor takes a function returning a type of the block. -/
def isReflexive (types : Array InductiveType) : Bool :=
  types.any fun t => t.ctors.any fun c =>
    anyDomain (fun d => d.isForall && hasOwnOcc types d) c.type

/-- The generated declarations the block is realised over. -/
public structure Model where
  /-- The enumeration tagging which type of the block a value belongs to, and at which indices. -/
  idx      : Name
  idxCtors : Array Name
  /-- The single inductive family the block collapses to. -/
  self     : Name
  /-- The model's constructors, in the block's order. -/
  ctors    : Array (Array Name)

/-- `M params (Idx.mkⱼ params indices)`, the family standing for the block's type at `j`. -/
def Model.app (m : Model) (b : Block) (j : Nat) (indices : Array Expr) : Expr :=
  mkApp (mkAppN (mkConst m.self b.lvls) b.params)
    (mkAppN (mkConst m.idxCtors[j]! b.lvls) (b.params ++ indices))

/--
Every occurrence of one of the block's types, rewritten as the family at that type's index.

An index argument is rewritten too, though `indApp?` refuses to call such an application an
occurrence. The two are not in disagreement: an occurrence there is unsound in general, and giving it
an image is what lets the kernel say so of the model rather than leaving the block without one. The
image is faithful: its index mentions the family, so it is no more a recursive argument than the
occurrence it stands for was.
-/
partial def Model.rewrite (m : Model) (b : Block) (e : Expr) : Expr :=
  e.replace fun t => (b.indApp?' t).map fun (j, indices) => m.app b j (indices.map (m.rewrite b))

/--
Declare the index enumeration and the single family, and check both.

The family's constructors are the block's, with every occurrence of one of the block's types
replaced by the family at that type's index. A constructor mentioning one of the block's types any
other way has no image here, and gives up rather than carrying the mention over: in the environment
the kernel certifies against those types do not exist yet.
-/
def mkModel (b : Block) (isUnsafe : Bool) (pre : Name) : MetaM (Option Model) := do
  let idx := pre ++ `Idx
  let idxCtors := (Array.range b.types.size).map fun i => idx ++ Name.mkSimple s!"mk{i}"
  let idxSelf := mkAppN (mkConst idx b.lvls) b.params
  -- the enumeration has to hold every index of every type of the block, and stay out of `Prop` so
  -- that the motive dispatch may eliminate into a sort
  let mut idxLevel := Level.one
  let mut idxCtorTypes := #[]
  for i in [0 : b.types.size] do
    let (ty, l) ← b.withIndices i fun indices => do
      let mut l := Level.zero
      for x in indices do
        l := mkLevelMax' l (← getLevel (← inferType x))
      return (← mkForallFVars (b.params ++ indices) idxSelf, l)
    idxLevel := mkLevelMax' idxLevel l
    idxCtorTypes := idxCtorTypes.push ty
  addDecl (.inductDecl b.lparams b.nparams
    [{ name := idx, type := ← mkForallFVars b.params (mkSort idxLevel)
       ctors := (idxCtors.zip idxCtorTypes).toList.map fun (n, t) => { name := n, type := t } }]
    isUnsafe)
  let self := pre ++ `M
  let m : Model := { idx, idxCtors, self, ctors := #[] }
  let mut ctors := #[]
  let mut decls := #[]
  for i in [0 : b.types.size] do
    let mut cs := #[]
    for j in [0 : b.types[i]!.ctors.length] do
      let c := b.types[i]!.ctors[j]!
      let name := self ++ Name.mkSimple s!"c{i}_{j}"
      let ty := m.rewrite b (← instantiateForall c.type b.params)
      if hasOwnOcc b.types ty then return none
      cs := cs.push name
      decls := decls.push ({ name, type := ← mkForallFVars b.params ty } : Constructor)
    ctors := ctors.push cs
  addDecl (.inductDecl b.lparams b.nparams
    [{ name := self, ctors := decls.toList
       type := ← mkForallFVars b.params (.forallE `i idxSelf (mkSort b.level) .default) }]
    isUnsafe)
  return some { m with ctors }

/-- The `u` a recursor eliminates at, as `init_elim_level` picks it. -/
private def freshElimParam (lparams : List Name) : Name := go `u 1 (lparams.length + 1)
where
  go (u : Name) (i fuel : Nat) : Name :=
    match fuel with
    | 0 => u
    | fuel + 1 =>
      if lparams.contains u then go (Name.appendIndexAfter `u i) (i + 1) fuel else u

/--
Derive the recursors the block introduces, and the term realising each of them.

The types and the rules are built the way `add_inductive_fn` builds them, since they are what the
kernel is asked to declare; the realisation is `M.rec` at a motive that dispatches through
`Idx.rec`, which reduces away as soon as the index is one of the enumeration's constructors.
-/
def mkRecursors (b : Block) (m : Model) : MetaM (Array RestoredRec × Array Expr) := do
  let lvls := b.lvls
  -- mutually inductive predicates eliminate only into `Prop`
  let elim : Level := if b.level.isNeverZero then .param (freshElimParam b.lparams) else .zero
  let recLvls := if elim.isParam then elim :: lvls else lvls
  let recLparams := match elim with | .param u => u :: b.lparams | _ => b.lparams
  let mut motiveDecls := #[]
  for i in [0 : b.types.size] do
    let ty ← b.withIndices i fun indices =>
      mkForallFVars indices (.forallE `t (b.app i indices) (mkSort elim) .default)
    motiveDecls := motiveDecls.push ((`motive).appendIndexAfter (i + 1), ty)
  withLocals motiveDecls fun motives => do
  let mut minorDecls := #[]
  let mut minorIdx : NameMap Nat := {}
  for i in [0 : b.types.size] do
    for c in b.types[i]!.ctors do
      let ty ← forallTelescope (← instantiateForall c.type b.params) fun fields concl => do
        let mut ihs := #[]
        for f in fields do
          let some ih ← b.underField true f (← f.fvarId!.getType)
              (fun j indices t => mkApp (mkAppN motives[j]! indices) t) | continue
          ihs := ihs.push ((← f.fvarId!.getUserName).appendAfter "_ih", ih)
        withLocals ihs fun vs => do
          let some (i', indices) := b.indApp? concl
            | throwError "'{c.name}' does not return a type of its own block at its parameters"
          mkForallFVars fields (← mkForallFVars vs (mkApp (mkAppN motives[i']! indices)
            (mkAppN (mkConst c.name lvls) (b.params ++ fields))))
      minorIdx := minorIdx.insert c.name minorDecls.size
      minorDecls := minorDecls.push (c.name.replacePrefix b.types[i]!.name .anonymous, ty)
  withLocals minorDecls fun minors => do
  let mRec := mkRecName m.self
  let mRecLparams := (← getConstInfoRec mRec).levelParams
  unless mRecLparams.length == b.lparams.length + 1 || !elim.isParam do
    throwError "the model eliminates only into `Prop` but the block does not"
  let mRecLvls := if mRecLparams.length == b.lparams.length + 1 then elim :: lvls else lvls
  -- `fun i x => motive_i indices x`, which the model's recursor takes in place of the block's
  -- motives: an enumeration constructor carries exactly the indices its motive expects
  let idxSelf := mkAppN (mkConst m.idx lvls) b.params
  let dispatch := Expr.lam `idx idxSelf
    (mkApp (mkAppN (mkConst (mkRecName m.idx) (mkLevelMax' b.level (mkLevelSucc elim) :: lvls))
       (b.params ++ #[Expr.lam `i idxSelf
          (.forallE `x (mkApp (mkAppN (mkConst m.self lvls) b.params) (.bvar 0)) (mkSort elim)
             .default) .default] ++ motives))
       (.bvar 0)) .default
  let mut recs : Array RestoredRec := #[]
  let mut vals : Array Expr := #[]
  for i in [0 : b.types.size] do
    let (type, val) ← b.withIndices i fun indices =>
      withLocalDeclD `t (b.app i indices) fun major => do
        let type ← mkForallFVars b.params (← mkForallFVars motives (← mkForallFVars minors
          (← mkForallFVars (indices.push major) (mkApp (mkAppN motives[i]! indices) major))))
        let val ← mkLambdaFVars (b.params ++ motives ++ minors ++ indices ++ #[major])
          (mkAppN (mkConst mRec mRecLvls) (b.params ++ #[dispatch] ++ minors ++
            #[mkAppN (mkConst m.idxCtors[i]! lvls) (b.params ++ indices), major]))
        return (type.inferImplicit
          (b.nparams + motives.size + minors.size + indices.size + 1) false, val)
    let mut rules : Array (Name × Nat × Expr) := #[]
    for c in b.types[i]!.ctors do
      let rule ← forallTelescope (← instantiateForall c.type b.params) fun fields _ => do
        let mut ihs := #[]
        for f in fields do
          let some ih ← b.underField false f (← f.fvarId!.getType)
              (fun j indices t => mkAppN (mkConst (mkRecName b.types[j]!.name) recLvls)
                 (b.params ++ motives ++ minors ++ indices ++ #[t])) | continue
          ihs := ihs.push ih
        let some mi := minorIdx.find? c.name | throwError "no minor premise for '{c.name}'"
        let rhs ← mkLambdaFVars (b.params ++ motives ++ minors ++ fields)
          (mkAppN minors[mi]! (fields ++ ihs))
        return (c.name, fields.size, rhs)
      rules := rules.push rule
    -- no rule needs a proof, but the kernel asks for an answer to each of them
    recs := recs.push { name := mkRecName b.types[i]!.name, levelParams := recLparams, type,
                        numIndices := b.nindices[i]!, rules,
                        proofs := rules.map fun _ => none }
    vals := vals.push val
  return (recs, vals)

/--
Add a definition realising one of the block's constants over the model.

`sur` renames the block's constants out of the way where they already exist. Under the naming the
kernel uses it is the identity, so the definitions carry the declaration's own names and the rules
the kernel states need no translation to be about the model.
-/
def Block.realise (b : Block) (sur : Name → Name) (isUnsafe : Bool) (n : Name) (lps : List Name)
    (ty val : Expr) : MetaM Unit := do
  let mut own : NameSet := {}
  for t in b.types do
    own := own.insert t.name |>.insert (mkRecName t.name)
    for c in t.ctors do
      own := own.insert c.name
  let fix (e : Expr) : Expr := e.replace fun
    | .const c us => if own.contains c then some (.const (sur c) us) else none
    | _ => none
  addDecl (.defnDecl { name := sur n, levelParams := lps, type := fix ty, value := fix val
                       hints := .abbrev, safety := if isUnsafe then .unsafe else .safe })

/--
Realise the block's types and constructors, which has to happen before the recursors are derived
rather than after: deriving them opens telescopes over the block's own types, and in the environment
the kernel certifies against these definitions are the only thing those names stand for.
-/
def mkDataRealisations (b : Block) (m : Model) (sur : Name → Name) (isUnsafe : Bool) :
    MetaM Unit := do
  -- every type first: a constructor of one may mention another
  for i in [0 : b.types.size] do
    b.realise sur isUnsafe b.types[i]!.name b.lparams b.types[i]!.type
      (← b.withIndices i fun indices => mkLambdaFVars (b.params ++ indices) (m.app b i indices))
  for i in [0 : b.types.size] do
    for j in [0 : b.types[i]!.ctors.length] do
      b.realise sur isUnsafe b.types[i]!.ctors[j]!.name b.lparams b.types[i]!.ctors[j]!.type
        (mkConst m.ctors[i]![j]! b.lvls)

/-- Realise the block's recursors as the terms `mkRecursors` derived. -/
def mkRecRealisations (b : Block) (sur : Name → Name) (isUnsafe : Bool)
    (recs : Array RestoredRec) (vals : Array Expr) : MetaM Unit := do
  for i in [0 : recs.size] do
    b.realise sur isUnsafe recs[i]!.name recs[i]!.levelParams recs[i]!.type vals[i]!

/-- What the block's certificate consists of, beyond the environment the generator built. -/
public structure Result where
  /-- The recursors the block introduces, derived from the model rather than read back. -/
  recs      : Array RestoredRec
  recursive : Bool
  reflexive : Bool
  model     : Model

/--
Build the model for a mutual inductive block and realise the block over it. `none` if the block is
not one this handles: a single type, or one whose types do not all end in the same sort.
-/
public def buildModelFor (lparams : List Name) (nparams : Nat) (types : Array InductiveType)
    (isUnsafe : Bool) (pre : Name) (sur : Name → Name) : MetaM (Option Result) := do
  if types.size < 2 then return none
  forallBoundedTelescope types[0]!.type nparams (whnfType := true) fun params _ => do
    if params.size != nparams then return none
    let shape : Block := { lparams, nparams, types, params, nindices := #[], level := .zero }
    let mut nindices := #[]
    let mut level? : Option Level := none
    for i in [0 : types.size] do
      let some ty ← shape.instantiateParams i | return none
      let some (n, l) ← forallTelescopeReducing ty fun indices concl => do
          let .sort l ← whnf concl | return none
          return some (indices.size, l)
        | return none
      -- the kernel insists on this, so a block that fails it is not one to build a model for
      if level?.any (!·.isEquiv l) then return none
      nindices := nindices.push n
      level? := some l
    let some level := level? | return none
    let b : Block := { lparams, nparams, types, params, nindices, level }
    let some m ← mkModel b isUnsafe pre | return none
    mkDataRealisations b m sur isUnsafe
    let (recs, vals) ← mkRecursors b m
    mkRecRealisations b sur isUnsafe recs vals
    return some { recs, recursive := isRecursive types, reflexive := isReflexive types, model := m }

/--
Certify a mutual inductive block the kernel is about to declare, by collapsing it to a single
family. Returns the environment the model was built in along with the recursors derived from it, or
`none` if the block is not one this reduces, in which case the kernel declares it itself.

Nothing here can license a declaration: the model and the realisations go into a scratch environment
the kernel keeps only to look the realisations up in, and the only possible effect is to reject.
-/
public def certifyCore (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : Array InductiveType) (isUnsafe : Bool) (sur : Name → Name) :
    IO (Except String (Option NestedGen.Certificate)) := do
  let ctx : Core.Context := {
    fileName := "<mutual inductive certificate>"
    fileMap := default
    -- the certificate has to be decided here, not deferred to a task nobody waits on
    options := Elab.async.set {} false
    -- a heartbeat exception would reject a declaration for being slow to certify
    maxHeartbeats := 0
  }
  let act : MetaM (Option Result) := do
    let some first := types[0]? | return none
    -- the realisation carries the declaration's own names, so the kernel's goals need no
    -- translation; the model sits under a prefix, out of the way of the names it realises
    buildModelFor lparams nparams types isUnsafe (`_certify ++ first.name) sur
  match ← ((MetaM.run' act : CoreM (Option Result)).run ctx { env }).toIO' with
  | .ok (none, _) => return .ok none
  | .ok (some res, s) =>
    return .ok (some { env := s.env.toKernelEnv, recs := res.recs, recursive := res.recursive
                       reflexive := types.map fun _ => res.reflexive })
  | .error ex => return .error (← ex.toMessageData.toString)

/-- `buildModelFor`, reading the block out of the environment. -/
public def buildModel (n : Name) (pre : Name) : MetaM Result := do
  let iv ← getConstInfoInduct n
  let types ← iv.all.toArray.mapM fun m => do
    let jv ← getConstInfoInduct m
    let ctors ← jv.ctors.mapM fun c => do
      return { name := c, type := (← getConstInfo c).type : Constructor }
    return ({ name := m, type := jv.type, ctors } : InductiveType)
  -- the block is already present, so the realisation has to be named out of its way
  let some res ← buildModelFor iv.levelParams iv.numParams types iv.isUnsafe pre (`_surr ++ pre ++ ·)
    | throwError "'{n}' is not a mutual inductive block this reduces"
  return res

end MutualGen

end Lean.Meta
