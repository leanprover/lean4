/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.InferType

public section

namespace Lean.Compiler.LCNF

namespace UnreachableBranches

/--
The abstract domain of the interpreter. Representing sets of values
of a certain type.
-/
inductive Value where
  /--
  Undefined, could be anything we have no information.
  -/
  | bot
  /--
  All values are possible.
  -/
  | top
  /--
  A certain constructor with a certain sets of parameters is possible.
  -/
  | ctor (i : Name) (vs : Array Value)
  /--
  A set of values are possible.
  -/
  | choice (vs : List Value)
  deriving Inhabited

namespace Value

-- TODO: parameterize
def maxValueDepth := 8

protected partial def beq : Value → Value → Bool
  | bot, bot => true
  | top, top => true
  | ctor i1 vs1 , ctor i2 vs2 =>
    i1 == i2 && Array.isEqv vs1 vs2 Value.beq
  | choice vs1 , choice vs2 =>
    let isSubset as bs := as.all (fun a => bs.any fun b => Value.beq a b)
    isSubset vs1 vs2 && isSubset vs2 vs1
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

protected partial def toFormat : Value → Format
  | bot => "⊥"
  | top => "⊤"
  | ctor i vs =>
    if vs.isEmpty then
      format i
    else
      .paren <| format i ++ .join (vs.toList.map fun v => " " ++ Value.toFormat v)
  | choice vs =>
    .paren <| .joinSep (vs.map Value.toFormat) " | "

instance : Repr Value where
  reprPrec v _ := Value.toFormat v

def inductValOfCtor (ctorName : Name) (env : Environment) : InductiveVal := Id.run do
  let some (.ctorInfo info) ← env.find? ctorName | unreachable!
  let some (.inductInfo info) ← env.find? info.induct | unreachable!
  return info

mutual

/--
Fuse `v` into `vs`. That is do not only append but if we see that `v`
is a constructor that is already contained within `vs` try to detect
the difference between these values and merge them accordingly into a
choice node further down the tree.
-/
partial def addChoice (env : Environment) (vs : List Value) (v : Value) : List Value :=
  match vs, v with
  | [], v => [v]
  | v1@(ctor i1 vs1) :: cs, ctor i2 vs2 =>
    if i1 == i2 then
      ctor i1 (Array.zipWith (merge env) vs1 vs2) :: cs
    else
      v1 :: addChoice env cs v
  | _, _ => panic! s!"invalid addChoice {repr v} into {repr vs}"

/--
Merge two values into one. `bot` is the neutral element, `top` the annihilator.
-/
partial def merge (env : Environment) (v1 v2 : Value) : Value :=
  let newValue :=
    match v1, v2 with
    | bot, v | v, bot => v
    | top, _ | _, top => top
    | ctor i1 vs1, ctor i2 vs2 =>
      if i1 == i2 then
        ctor i1 (Array.zipWith (merge env) vs1 vs2)
      else
        choice [v1, v2]
    | choice vs1, choice vs2 =>
      choice (vs1.foldl (addChoice env) vs2)
    | choice vs, v | v, choice vs =>
      choice (addChoice env vs v)
  match newValue with
  | .top | .bot => newValue
  | .choice vs => cleanup vs
  | .ctor ctorName .. =>
    if eligible newValue && inductHasNumCtors ctorName env 1 then
      top
    else
      newValue
where
  cleanup (vs : List Value) : Value := Id.run do
    if vs.all eligible then
      let .ctor ctorName .. := vs.head! | unreachable!
      if inductHasNumCtors ctorName env vs.length then
        top
      else
        choice vs
    else
      choice vs

  inductHasNumCtors (ctorName : Name) (env : Environment) (n : Nat) : Bool := Id.run do
    let induct := inductValOfCtor ctorName env
    n == induct.numCtors

  @[inline]
  eligible (value : Value) : Bool := Id.run do
    let .ctor _ args := value | return false
    args.all (· == .top)

end

/--
Make sure constructors of recursive inductive datatypes can only occur once in each path.
Values at depth > `maxValueDepth` are also approximated at `top`.
We use this function to implement a simple widening operation for our abstract interpreter.
Recall the widening functions is used to ensure termination in abstract interpreters.
-/
partial def truncate (env : Environment) (v : Value) : Value :=
  go v {} maxValueDepth
where
  go (v : Value) (forbiddenTypes : NameSet) (remainingDepth : Nat) :=
    match remainingDepth with
    | 0 => top
    | remainingDepth + 1 =>
      match v with
      | ctor i vs =>
        let induct := inductValOfCtor i env
        if forbiddenTypes.contains induct.name then
          top
        else
          let cont forbiddenTypes' :=
            ctor i (vs.map (go · forbiddenTypes' remainingDepth))
          if induct.isRec then
            cont <| forbiddenTypes.insert induct.name
          else
            cont forbiddenTypes
      | choice vs =>
        let vs := vs.map (go · forbiddenTypes remainingDepth)
        if vs.elem top then
          top
        else
          choice vs
      | v => v

/-- Widening operator that guarantees termination in our abstract interpreter. -/
def widening (env : Environment) (v1 v2 : Value) : Value :=
  truncate env (merge env v1 v2)

/--
Check whether a certain constructor is part of a `Value` by name.
Note that both `top` and `bot` will always true here. For bot this is
because we have no information about the `Value` so just to be sure
we don't claim the absence of a certain constructor.
-/
partial def containsCtor : Value → Name → Bool
| .top .., _ => true
| .bot .., _ => true -- we don't know so better be safe than sorry
| .ctor i ..,  j => i == j
| .choice vs .., j => vs.any fun v => containsCtor v j

/--
Obtain the arguments of a certain constructor within the `Value`.
-/
partial def getCtorArgs : Value → Name → Option (Array Value)
| .ctor i args ..,  j => if i == j then some args else none
| .choice vs .., j => do
  for variant in vs do
    if let .ctor i args .. := variant then
      if i == j then
        return args
  none
| _, _ => none

partial def ofNat (n : Nat) : Value :=
  if n > maxValueDepth then
    .top
  else
    goSmall n
where
  goSmall : Nat → Value
  | 0 => .ctor ``Nat.zero #[]
  | n + 1 => .ctor ``Nat.succ #[goSmall n]

def ofLCNFLit : LCNF.LitValue → Value
| .nat n => ofNat n
-- TODO: Make this work for other numeric literal types.
| .uint8 _ | .uint16 _ | .uint32 _ | .uint64 _ | .usize _ => .top
-- TODO: We could make this much more precise but the payoff is questionable
| .str .. => .top

partial def proj (env : Environment) : Value → Nat → Value
| .ctor _ vs , i => vs.getD i bot
| .choice vs, i => vs.foldl (fun r v => widening env r (proj env v i)) bot
| v, _ => v

/--
We say that a `Value` is a literal iff it is only a tree of `Value.ctor`
nodes.
-/
partial def isLiteral : Value → Bool
| .ctor _ vs => vs.all isLiteral
| _ => false

/-
TODO: Add support for "Higher Order Literals", that is literals with
type parameters.
-/
/--
Attempt to turn a `Value` that is representing a literal into a set of
auxiliary declarations + the final `FVarId` of the declaration that
contains the actual literal. If it is not a literal return none.
-/
partial def getLiteral (v : Value) : CompilerM (Option ((Array (CodeDecl .pure)) × FVarId)) := do
  if isLiteral v then
    let literal ← go v
    return some literal
  else
    return none
where
  go : Value → CompilerM ((Array (CodeDecl .pure)) × FVarId)
  | .ctor ``Nat.zero #[] .. => do
    let decl ← mkAuxLetDecl <| .lit <| .nat <| 0
    return (#[.let decl], decl.fvarId)
  | .ctor ``Nat.succ #[val] .. => do
    let val := getNatConstant val + 1
    let decl ← mkAuxLetDecl <| .lit <| .nat <| val
    return (#[.let decl], decl.fvarId)
  | .ctor ctorName vs => do
    let some (.ctorInfo ctorInfo) := (← getEnv).find? ctorName | unreachable!
    let fields ← vs.mapM go
    let flatten acc := fun (decls, var) => (acc.fst ++ decls, acc.snd.push <| .fvar var)
    let (decls, args) :=
      fields.foldl (init := (#[], Array.replicate ctorInfo.numParams .erased)) flatten
    let letVal : LetValue .pure := .const ctorName [] args
    let letDecl ← mkAuxLetDecl letVal
    return (decls.push <| .let letDecl, letDecl.fvarId)
  | _ => unreachable!

  getNatConstant : Value → Nat
  | .ctor ``Nat.zero #[] .. => 0
  | .ctor ``Nat.succ #[val] .. => getNatConstant val + 1
  | _ => panic! "Not a well formed Nat constant Value"

end Value

/--
A map from function names to the `Value` that the abstract interpreter
produced for them.
-/
abbrev FunctionSummaries := PHashMap Name Value

private abbrev decLt (a b : Name × Value) : Bool :=
  Name.quickLt a.fst b.fst

private abbrev findAtSorted? (entries : Array (Name × Value)) (fid : Name) : Option Value :=
  entries.binSearch (fid, default) decLt |>.map Prod.snd

/--
Storing `FunctionSummaries` for all functions in a `.olean`.
-/
builtin_initialize functionSummariesExt : SimplePersistentEnvExtension (Name × Value) FunctionSummaries ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn := fun s ⟨e, n⟩ => s.insert e n
    exportEntriesFnEx? := some fun _ s _ => fun
      -- preserved for non-modules, make non-persistent at some point?
      | .private => s.toArray.qsort decLt
      | _ => #[]
    asyncMode := .sync  -- compilation is non-parallel anyway
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.1) (fun s ⟨e, n⟩ => s.insert e n)
  }

/--
Add a `Value` for a function name.
-/
def addFunctionSummary (env : Environment) (fid : Name) (v : Value) : Environment :=
  functionSummariesExt.addEntry env (fid, v)

/--
Obtain the `Value` for a function name if possible.
-/
def getFunctionSummary? (env : Environment) (fid : Name) : Option Value :=
  match env.getModuleIdxFor? fid with
  | some modIdx => findAtSorted? (functionSummariesExt.getModuleEntries env modIdx) fid
  | none        => functionSummariesExt.getState env |>.find? fid

/--
A map from variable identifiers to the `Value` produced by the abstract
interpreter for them.
-/
abbrev Assignment := Std.HashMap FVarId Value

/--
The context of `InterpM`.
-/
structure InterpContext where
  /--
  The list of `Decl`s we are operating on in `InterpM`. This can be
  a single declaration or a mutual block of declarations where their
  analysis might influence each other as we approach the fixpoint.
  -/
  decls     : Array (Decl .pure)
  /--
  The index of the function we are currently operating on in `decls.`
  -/
  currFnIdx : Nat := 0

structure InterpState where
  /--
  `Assignment`s of functions in the `InterpContext`.
  -/
  assignments : Array Assignment
  /--
  `Value`s of functions in the `InterpContext` use during computation of
  the fixpoint. Afterwards they are stored into the `Environment`.
  -/
  funVals     : Array Value

/--
The monad which powers the abstract interpreter.
-/
abbrev InterpM := ReaderT InterpContext StateRefT InterpState CompilerM

/--
Get the variable `Assignment` of the current function.
-/
def getAssignment : InterpM Assignment := do
  return (← get).assignments[(← read).currFnIdx]!

/--
Get the `Value` of a certain function in the current block by index.
-/
def getFunVal (funIdx : Nat) : InterpM Value := do
  return (← get).funVals[funIdx]!

def findFunVal? (declName : Name) : InterpM (Option Value) := do
  match (← read).decls.findIdx? (·.name == declName) with
  | some idx => return some (← getFunVal idx)
  | none => return none

/--
Run `f` on the variable `Assignment` of the current function.
-/
def modifyAssignment (f : Assignment → Assignment) : InterpM Unit := do
  let ctx ← read
  let currFnIdx := ctx.currFnIdx
  modify fun s => { s with assignments := s.assignments.modify currFnIdx f }

/--
Obtain the `Value` associated with `var` from the context of `InterpM`.
If none is available return `Value.bot`.
-/
def findVarValue (var : FVarId) : InterpM Value := do
  let assignment ← getAssignment
  return assignment.getD var .bot

/--
Find the value of `arg` using the logic of `findVarValue`.
-/
def findArgValue (arg : Arg .pure) : InterpM Value := do
  match arg with
  | .fvar fvarId => findVarValue fvarId
  | _ => return .top

/--
Update the assignment of `var` by merging the current value with `newVal`.
-/
def updateVarAssignment (var : FVarId) (newVal : Value) : InterpM Unit := do
  let env ← getEnv
  let val ← findVarValue var
  let updatedVal := .widening env val newVal
  modifyAssignment (·.insert var updatedVal)

/--
Set the value of `var` to `bot`.
-/
def resetVarAssignment (var : FVarId) : InterpM Unit := do
  modifyAssignment (·.insert var .bot)

/--
Widen the value of the current function by `v`.
-/
def updateCurrFnSummary (v : Value) : InterpM Unit := do
  let ctx ← read
  let env ← getEnv
  let currFnIdx := ctx.currFnIdx
  modify fun s => { s with funVals := s.funVals.modify currFnIdx (fun v' => .widening env v v') }

/--
Return true if the assignment of at least one parameter has been updated.
Furthermore if we see that `params.size != args.size` we know that this is
a partial application and set the values of the remaining parameters to
`top` since it is impossible to track what will happen with them from here on.
-/
def updateFunDeclParamsAssignment (params : Array (Param .pure)) (args : Array (Arg .pure)) :
    InterpM Bool := do
  let mut ret := false
  let env ← getEnv
  for param in params, arg in args do
    let paramVal ← findVarValue param.fvarId
    let argVal ← findArgValue arg
    let newVal := .widening env paramVal argVal
    if newVal != paramVal then
      modifyAssignment (·.insert param.fvarId newVal)
      ret := true
  /-
  This is a partial application, we can not know for sure what remaining
  arguments the local function is getting passed without a much more
  sophisticated analysis. Hence we will set all of the non applied ones
  to top.
  -/
  if params.size != args.size then
    for param in params[args.size...*] do
      ret := (← findVarValue param.fvarId) == .bot
      updateVarAssignment param.fvarId .top
  return ret

def updateFunDeclParamsTop (params : Array (Param .pure)) : InterpM Bool := do
  let mut ret := false
  for param in params do
    let paramVal ← findVarValue param.fvarId
    let newVal := .top
    if newVal != paramVal then
      modifyAssignment (·.insert param.fvarId newVal)
      ret := true
  return ret

private partial def resetNestedFunDeclParams : Code .pure → InterpM Unit
| .let _ k => resetNestedFunDeclParams k
| .jp decl k | .fun decl k => do
  decl.params.forM (resetVarAssignment ·.fvarId)
  /- We don't need to reset the parameters of decls
    nested in this one since they will be reset if this decl is used. -/
  resetNestedFunDeclParams k
| .cases cs =>
  cs.alts.forM (resetNestedFunDeclParams ·.getCode)
| .return .. | .unreach .. | .jmp .. => return ()

/--
The actual abstract interpreter on a block of `Code`.
-/
partial def interpCode : Code .pure → InterpM Unit
| .let decl k => do
  let val ← interpLetValue decl.value
  updateVarAssignment decl.fvarId val
  if let .fvar fvarId args := decl.value then
    if let some funDecl ← findFunDecl? fvarId then
      -- TODO: unclear how much we should reset in the case of partial applications
      interpFunCall funDecl args
  interpCode k
| .jp decl k | .fun decl k => do
  interpCode decl.value
  interpCode k
| .jmp fn args => do
  let jp ← getFunDecl fn
  args.forM handleFunArg
  interpFunCall jp args
| .cases cs => do
  let discrVal ← findVarValue cs.discr
  for alt in cs.alts do
    match alt with
    | .alt ctor params body =>
      if let some argValues := discrVal.getCtorArgs ctor then
        params.zip argValues |>.forM (fun (param, val) => updateVarAssignment param.fvarId val)
      else
        params.forM (updateVarAssignment ·.fvarId .top)
      interpCode body
    | .default body => interpCode body
| .return var => do
  handleFunVar var
  let val ← findVarValue var
  updateCurrFnSummary val
| .unreach .. => return ()
where
  /--
  The abstract interpreter on a `LetValue`.
  -/
  interpLetValue (letVal : LetValue .pure) : InterpM Value := do
    match letVal with
    | .lit val => return .ofLCNFLit val
    | .proj _ idx struct =>
      let env ← getEnv
      return (← findVarValue struct).proj env idx
    | .const declName _ args =>
      let env ← getEnv
      args.forM handleFunArg
      match (← getDecl? declName) with
      | some ⟨_, decl⟩ =>
        if decl.getArity == args.size then
          match getFunctionSummary? env declName with
          | some v => return v
          | none => return (← findFunVal? declName).getD .top
        else
          return .top
      | none =>
        let some (.ctorInfo info) := env.find? declName | return .top
        let args := args[info.numParams...*].toArray
        if info.numFields == args.size then
          return .ctor declName (← args.mapM findArgValue)
        else
          return .top
    | .fvar _ args =>
      args.forM handleFunArg
      /-
      Since free variables in `LetValue`s cannot be of the form
      `let x := y` after a simplifier pass we know they are in fact a
      partially applied function, we cannot know anything about the result
      of a partially applied function.
      -/
      return .top
    | .erased => return .top

  handleFunArg (arg : Arg .pure) : InterpM Unit := do
    if let .fvar fvarId := arg then
      handleFunVar fvarId

  /--
  If we see a function being passed as an argument to a higher order
  function we cannot know what arguments it will be passed further
  down the line. Hence we set all of its arguments to `top` since anything
  is possible.
  -/
  handleFunVar (var : FVarId) : InterpM Unit := do
    if let some funDecl ← findFunDecl? var then
      let updated ← updateFunDeclParamsTop funDecl.params
      if updated then
        /- We must reset the value of nested function declaration
        parameters since they depend on `args` values. -/
        resetNestedFunDeclParams funDecl.value
        interpCode funDecl.value

  interpFunCall (funDecl : FunDecl .pure) (args : Array (Arg .pure)) : InterpM Unit := do
    let updated ← updateFunDeclParamsAssignment funDecl.params args
    if updated then
      /- We must reset the value of nested function declaration
      parameters since they depend on `args` values. -/
      resetNestedFunDeclParams funDecl.value
      interpCode funDecl.value


/--
Rerun the abstract interpreter on all declarations except of the unsafe
ones. Return whether any `Value` got updated in the process.
-/
def inferStep : InterpM Bool := do
  let ctx ← read
  for h : idx in *...ctx.decls.size do
    let decl := ctx.decls[idx]
    if !decl.safe then
      continue

    let currentVal ← getFunVal idx
    withReader (fun ctx => { ctx with currFnIdx := idx }) do
      decl.params.forM fun p => updateVarAssignment p.fvarId .top
      match decl.value with
      | .code code .. =>
        withTraceNode `Compiler.elimDeadBranches (fun _ => return m!"Analyzing {decl.name}") do
          interpCode code
      | .extern .. => updateCurrFnSummary .top
    let newVal ← getFunVal idx
    if currentVal != newVal then
      return true
  return false

/--
Run `inferStep` until it reaches a fix point.
-/
partial def inferMain (n : Nat := 0) : InterpM Unit := do
  let ctx ← read
  modify fun s => { s with assignments := ctx.decls.map fun _ => {} }
  let modified ← inferStep
  if modified then
    inferMain (n + 1)
  else
    trace[Compiler.elimDeadBranches] m!"Termination after {n} steps"
    return ()

/--
Use the information produced by the abstract interpreter to:
- Eliminate branches that we know cannot be hit
- Eliminate values that we know have to be constants.
-/
partial def elimDead (assignment : Assignment) (decl : Decl .pure) : CompilerM (Decl .pure) := do
  trace[Compiler.elimDeadBranches] s!"Eliminating {decl.name} with {repr (← assignment.toArray |>.mapM (fun (name, val) => do return (toString (← getBinderName name), val)))}"
  return { decl with value := (← decl.value.mapCodeM go) }
where
  go (code : Code .pure) : CompilerM (Code .pure) := do
    match code with
    | .let decl k =>
      return code.updateLet! decl (← go k)
    | .jp decl k | .fun decl k =>
      return code.updateFun! (← decl.updateValue (← go decl.value)) (← go k)
    | .cases cs =>
      let discrVal := assignment.getD cs.discr .bot
      let processAlt typ alt := do
        match alt with
        | .alt ctor args body =>
          if discrVal.containsCtor ctor then
            let constantInfos ← args.filterMapM fun param => do
              if let some val := assignment[param.fvarId]? then
                if let some literal ← val.getLiteral then
                  return some (param, literal)
              return none
            if constantInfos.size != 0 then
              let (body, subst) ← constantInfos.foldlM (init := (← go body, {})) fun (body, subst) (param, decls, var) => do
                return (attachCodeDecls decls body, subst.insert param.fvarId (.fvar var))
              let body ← replaceFVars body subst false
              return alt.updateCode body
            else
              return alt.updateCode (← go body)
          else
            trace[Compiler.elimDeadBranches] s!"Threw away cases {← getBinderName cs.discr} branch {ctor}"
            eraseCode alt.getCode
            return alt.updateCode <| .unreach typ
        | .default body => return alt.updateCode (← go body)
      return code.updateAlts! (← cs.alts.mapMonoM <| processAlt cs.resultType)
    | .jmp .. | .return .. | .unreach .. => return code

end UnreachableBranches

open UnreachableBranches in
def Decl.elimDeadBranches (decls : Array (Decl .pure)) : CompilerM (Array (Decl .pure)) := do
  /-
  We sort declarations by size here to ensure that when we restart in inferStep it will mostly be
  small declarations that get re-analyzed.
  -/
  let decls := decls.qsort (fun l r => (l.size, l.name.toString).lexLt (r.size, r.name.toString))
  let mut assignments := decls.map fun _ => {}
  let initialVal i :=
    /-
    Non terminating functions are marked as unsafe, we don't want to run
    any analysis on them since we cannot be sure they will ever return
    the constructor that we inferred for them. For more information
    refer to the docstring of `Decl.safe`.
    -/
    if decls[i]!.safe then .bot else .top
  let mut funVals := decls.size.fold (init := .empty) fun i _ p => p.push (initialVal i)
  let ctx := { decls }
  let mut state := { assignments, funVals }
  (_, state) ←
    withTraceNode `Compiler.elimDeadBranches (fun _ => return m!"Analyzing block: {decls.map (·.name)}")
      inferMain |>.run ctx |>.run state
  funVals := state.funVals
  assignments := state.assignments
  modifyEnv fun e =>
    decls.size.fold (init := e) fun i _ env =>
      addFunctionSummary env decls[i].name funVals[i]!

  decls.mapIdxM fun i decl => if decl.safe then elimDead assignments[i]! decl else return decl

def elimDeadBranches : Pass :=
  { name := `elimDeadBranches, run := Decl.elimDeadBranches, phase := .mono, phaseOut := .mono }

builtin_initialize
  registerTraceClass `Compiler.elimDeadBranches (inherited := true)

end Lean.Compiler.LCNF
