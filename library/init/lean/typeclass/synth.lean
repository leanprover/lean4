/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Typeclass synthesis using tabled resolution.

Note: this file will be need to be updated once the unifier is implemented in Lean.
-/
prelude
import init.lean.expr init.lean.environment init.lean.class init.lean.metavarcontext
       init.lean.typeclass.context init.data.persistenthashmap
       init.data.queue

namespace Lean
namespace TypeClass

structure TypedExpr : Type :=
(val type : Expr)

instance TypedExpr.HasToString : HasToString TypedExpr :=
⟨λ ⟨val, type⟩ => "TypedExpr(" ++ toString val ++ ", " ++ toString type ++ ")"⟩

instance TypedExpr.Inhabited : Inhabited TypedExpr :=
⟨⟨default _, default _⟩⟩

structure Node : Type :=
(anormSubgoal : Expr)
(ctx          : Context)
(futureAnswer : TypedExpr)

instance Node.Inhabited : Inhabited Node :=
⟨⟨default _, {}, default _⟩⟩

structure ConsumerNode extends Node :=
(remainingSubgoals : List Expr)

instance ConsumerNode.Inhabited : Inhabited ConsumerNode :=
⟨⟨default _, default _⟩⟩

inductive Waiter : Type
| consumerNode : ConsumerNode → Waiter
| root         : Waiter

-- TODO(dselsam): support local instances once elaborator is in Lean
inductive Instance : Type
| lDecl : LocalDecl → Instance
| const : Name → Instance

structure GeneratorNode extends Node :=
(remainingInstances : List Instance)

instance GeneratorNode.Inhabited : Inhabited GeneratorNode :=
⟨⟨default _, default _⟩⟩

structure TableEntry : Type :=
(waiters    : Array Waiter)
(answers    : Array TypedExpr := Array.empty)

structure TCState : Type :=
(env            : Environment)
(finalAnswer    : Option TypedExpr                  := none)
(mainMVar       : Expr                              := default _)
(generatorStack : Array GeneratorNode               := Array.empty)
(consumerStack  : Array ConsumerNode                := Array.empty)
(resumeQueue    : Queue (ConsumerNode × TypedExpr)  := {})
(tableEntries   : PersistentHashMap Expr TableEntry := PersistentHashMap.empty)

abbrev TCMethod : Type → Type := EState String TCState

-- TODO(dselsam): once `whnf` is ready, need a more expensive pass as a backup,
-- that creates locals and calls `whnf` on every recursion.
-- See: [type_context.cpp] optional<name> type_context_old::is_full_class(expr type)
-- TODO(dselsam): check if we need to call `get_decl()` as well in the `const` case.
def quickIsClass (env : Environment) : Expr → Option (Option Name)
| Expr.elet _ _ _ _ => none
| Expr.proj _ _ _   => none
| Expr.mdata _ e    => quickIsClass e
| Expr.const n _    => if isClass env n then some (some  n) else none
| Expr.pi _ _ _ b   => quickIsClass b
| Expr.app e _      =>
  let f := e.getAppFn;
  if f.isConst && isClass env f.constName then some (some f.constName)
  else if f.isLambda then none
  else some none
| _            => some none

def newSubgoal (waiter : Waiter) (ctx : Context) (mvar : Expr) : TCMethod Unit :=
do let mvarType := ctx.eInfer mvar;
   isClassStatus ← get >>= λ ϕ => pure $ quickIsClass ϕ.env mvarType;
   match isClassStatus with
   | none      => throw $ "quickIsClass not sufficient to show `" ++ toString mvarType ++ "` is a class"
   | some none => throw $ "found non-class goal `" ++ toString mvarType ++ "`"
   | some (some n) => do
     gNode ← get >>= λ ϕ => pure {
       GeneratorNode .
       ctx                := ctx,
       anormSubgoal       := Context.αNorm $ ctx.eInstantiate mvarType,
       futureAnswer       := ⟨mvar, mvarType⟩,
       remainingInstances := (getClassInstances ϕ.env n).map Instance.const
     };
     let tableEntry : TableEntry := { waiters := [waiter].toArray };
     modify $ λ ϕ => {
       generatorStack := ϕ.generatorStack.push gNode,
       tableEntries   := ϕ.tableEntries.insert gNode.anormSubgoal tableEntry,
       .. ϕ
     }

partial def introduceMVars (lctx : LocalContext) (locals : Array Expr) : Context → Expr → Expr → Array Expr → Context × Expr × Expr × Array Expr
| ctx, instVal, Expr.pi _ info domain body, mvars => do
  let ⟨mvar, ctx⟩ := (Context.eNewMeta $ lctx.mkForall locals domain).run ctx;
  let arg := mkApp mvar locals.toList; -- TODO(dselsam): rm toList
  let instVal := Expr.app instVal arg;
  let instType := body.instantiate1 arg;
  let mvars := if info.isInstImplicit then mvars.push mvar else mvars;
  introduceMVars ctx instVal instType mvars

| ctx, instVal, instType, mvars => (ctx, instVal, instType, mvars)

partial def introduceLocals : Nat → LocalContext → Array Expr → Expr → LocalContext × Expr × Array Expr
| nextIdx, lctx, ls, Expr.pi name info domain body =>
  let idxName : Name := mkNumName (mkSimpleName "_tmp") nextIdx;
  let ⟨lDecl, lctx⟩ := lctx.mkLocalDecl idxName name domain info;
  let l : Expr := Expr.fvar idxName;
  introduceLocals (nextIdx + 1) lctx (ls.push l) (body.instantiate1 l)

| _, lctx, ls, e => (lctx, e, ls)

def tryResolve (ctx : Context) (futureAnswer : TypedExpr) (instTE : TypedExpr) : TCMethod (Option (Context × List Expr)) :=
do let ⟨mvar, mvarType⟩ := futureAnswer;
   let ⟨instVal, instType⟩ := instTE;
   let ⟨lctx, mvarType, locals⟩ := introduceLocals 0 {} Array.empty mvarType;
   let ⟨ctx, instVal, instType, newMVars⟩ := introduceMVars lctx locals ctx instVal instType Array.empty;
   match (Context.eUnify mvarType instType *> Context.eUnify mvar (lctx.mkLambda locals instVal)).run ctx with
   | EState.Result.error msg   _ => pure none
   | EState.Result.ok    _   ctx => pure $ some $ (ctx, newMVars.toList) -- TODO(dselsam): rm toList

def newConsumerNode (node : Node) (ctx : Context) (newMVars : List Expr) : TCMethod Unit :=
let cNode : ConsumerNode := { remainingSubgoals := newMVars, ctx := ctx, .. node };
modify $ λ ϕ => { consumerStack := ϕ.consumerStack.push cNode, .. ϕ }

def resume : TCMethod Unit :=
do ((cNode, answer), resumeQueue) ← get >>= λ ϕ =>
     match ϕ.resumeQueue.dequeue? with
     | none => throw "resume found nothing to resume"
     | some result => pure result;
   match cNode.remainingSubgoals with
   | []           => throw "resume found no remaining subgoals"
   | (mvar::rest) => do
     result : Option (Context × List Expr) ←
       tryResolve cNode.ctx ⟨mvar, cNode.ctx.eInfer mvar⟩ answer;
     modify $ λ ϕ => { resumeQueue := resumeQueue, .. ϕ };
     match result with
     | none => pure ()
     | some (ctx, newMVars) => newConsumerNode cNode.toNode ctx (newMVars ++ rest)

def wakeUp (answer : TypedExpr) : Waiter → TCMethod Unit
| Waiter.root               => modify $ λ ϕ => { finalAnswer := some answer .. ϕ }
| Waiter.consumerNode cNode => modify $ λ ϕ => { resumeQueue := ϕ.resumeQueue.enqueue (cNode, answer), .. ϕ }

def newAnswer (anormSubgoal : Expr) (answer : TypedExpr) : TCMethod Unit :=
do lookupStatus ← get >>= λ ϕ => pure $ ϕ.tableEntries.find anormSubgoal;
   match lookupStatus with
   | none       => throw $ "[newAnswer]: " ++ toString anormSubgoal ++ " not found in table!"
   | some entry => do
     if entry.answers.any (λ answer₁ => answer₁.type == answer.type) then pure() else do
       let newEntry : TableEntry := { answers := entry.answers.push answer .. entry };
       modify $ λ ϕ => { tableEntries := ϕ.tableEntries.insert anormSubgoal newEntry .. ϕ };
       entry.waiters.mfor (wakeUp answer)

def consume : TCMethod Unit :=
do cNode ← get >>= λ ϕ => pure ϕ.consumerStack.back;
   match cNode.remainingSubgoals with
   | [] => do
     let answer : TypedExpr := {
       val := cNode.ctx.eInstantiate cNode.futureAnswer.val,
       type := cNode.ctx.eInstantiate cNode.futureAnswer.type
     };
     when (Context.eHasTmpMVar answer.val || Context.eHasTmpMVar answer.type) $
       throw $ "answer " ++ toString answer ++ " not fully instantiated";
     modify $ λ ϕ => { consumerStack := ϕ.consumerStack.pop .. ϕ };
     newAnswer cNode.anormSubgoal answer

   | mvar::rest => do
     let anormSubgoal : Expr := Context.αNorm (cNode.ctx.eInstantiate $ cNode.ctx.eInfer mvar);
     let waiter : Waiter := Waiter.consumerNode cNode;
     lookupStatus ← get >>= λ ϕ => pure $ ϕ.tableEntries.find anormSubgoal;
     match lookupStatus with
     | none => do
       newSubgoal waiter cNode.ctx mvar;
       modify $ λ ϕ => { consumerStack := ϕ.consumerStack.pop .. ϕ }
     | some entry => modify $ λ ϕ => {
                        consumerStack := ϕ.consumerStack.pop,
                        resumeQueue   := entry.answers.foldl (λ rq answer => rq.enqueue (cNode, answer)) ϕ.resumeQueue,
                        tableEntries  := ϕ.tableEntries.insert anormSubgoal { waiters := entry.waiters.push waiter, .. entry },
                        .. ϕ }

def constNameToTypedExpr (ctx : Context) (instName : Name) : TCMethod (TypedExpr × Context) :=
do lookupStatus ← get >>= λ ϕ => pure $ ϕ.env.find instName;
   match lookupStatus with
   | none       => throw $ "instance " ++ toString instName ++ " not found in env"
   | some cInfo =>
     let ⟨uMetas, ctx⟩ : List Level × Context :=
       cInfo.lparams.foldl (λ ⟨uMetas, ctx⟩ _ =>
                              let ⟨uMeta, ctx⟩ := Context.uNewMeta.run ctx;
                              ⟨uMeta::uMetas, ctx⟩)
                            ([], ctx);
     let instVal          := Expr.const instName uMetas;
     let instType      := cInfo.instantiateTypeUnivParams uMetas;
     pure ⟨⟨instVal, instType⟩, ctx⟩

def generate : TCMethod Unit :=
do gNode ← get >>= λ ϕ => pure ϕ.generatorStack.back;
   match gNode.remainingInstances with
   | []                  => throw "[generate] gNode.remainingInstances.isEmpty"
   | inst::insts => do
     ⟨instTE, ctx⟩ ← match inst with
                     | Instance.const n     => constNameToTypedExpr gNode.ctx n
                     | Instance.lDecl lDecl => throw "local instances not yet supported";
     result : Option (Context × List Expr) ← tryResolve ctx gNode.futureAnswer instTE;
     nextGeneratorStack ←
       if insts.isEmpty
       then get >>= λ ϕ => pure ϕ.generatorStack.pop
       else get >>= λ ϕ => pure $ ϕ.generatorStack.modify
                                  (ϕ.generatorStack.size-1)
                                  (λ gNode => { remainingInstances := insts .. gNode });
     modify $ λ ϕ => { generatorStack := nextGeneratorStack, .. ϕ };
     match result with
     | none => pure ()
     | some (ctx, newMVars) => newConsumerNode gNode.toNode ctx newMVars

def step : TCMethod Unit :=
do ϕ ← get;
   if !ϕ.resumeQueue.isEmpty then resume
   else if !ϕ.consumerStack.isEmpty then consume
   else if !ϕ.generatorStack.isEmpty then generate
   else throw "FAILED TO SYNTHESIZE"

partial def synthCoreFueled (ctx₀ : Context) (goalType : Expr) : Nat → TCMethod TypedExpr
| 0   => throw "[synthCore] out of fuel"
| n+1 => do
  step;
  finalAnswer ← get >>= λ ϕ => pure ϕ.finalAnswer;
  match finalAnswer with
  | none => synthCoreFueled n
  | some ⟨answerVal, answerType⟩ => pure ⟨answerVal, answerType⟩

def synthCore (ctx₀ : Context) (goalType : Expr) (fuel : Nat) : TCMethod TypedExpr :=
do let ⟨mvar, ctx⟩ := (Context.eNewMeta goalType).run ctx₀;
   newSubgoal Waiter.root ctx mvar;
   modify $ λ ϕ => { mainMVar := mvar .. ϕ };
   synthCoreFueled ctx₀ goalType fuel

def collectUReplacements : List Level → Context → Array (Level × Level) → Array Level
                             → Context × Array (Level × Level) × Array Level
| [],    ctx, uReplacements, fLevels => (ctx, uReplacements, fLevels)

| l::ls, ctx, uReplacements, fLevels =>
  if l.hasMVar then
    let ⟨uMeta, ctx⟩ := Context.uNewMeta.run ctx;
    collectUReplacements ls ctx (uReplacements.push (uMeta,l)) (fLevels.push uMeta)
  else
    collectUReplacements ls ctx uReplacements (fLevels.push l)

def collectEReplacements (env : Environment) (lctx : LocalContext) (locals : Array Expr)
  : Expr → List Expr → Context → Array (Expr × Expr) → Array Expr
    → Context × Array (Expr × Expr) × Array Expr
| _,               [],        ctx, eReplacements, fArgs => (ctx, eReplacements, fArgs)

| Expr.pi _ _ d b, arg::args, ctx, eReplacements, fArgs =>
  if isOutParam d then
    let ⟨eMeta, ctx⟩ := (Context.eNewMeta $ lctx.mkForall locals d).run ctx;
    let fArg : Expr  := mkApp eMeta locals.toList;
    collectEReplacements (b.instantiate1 fArg) args ctx (eReplacements.push (eMeta, arg)) (fArgs.push fArg)
  else
    collectEReplacements (b.instantiate1 arg) args ctx eReplacements (fArgs.push arg)

| _, arg::args, _, _, _ => panic! "TODO(dselsam): this case not yet handled"

def preprocessForOutParams (env : Environment) (goalType : Expr) : Context × Expr × Array (Level × Level) × Array (Expr × Expr) :=
if !goalType.hasMVar && goalType.getAppFn.isConst && !hasOutParams env goalType.getAppFn.constName
then ({}, goalType, Array.empty, Array.empty)
else
  let ⟨lctx, bodyGoalType, locals⟩ := introduceLocals 0 {} Array.empty goalType;
  let f := goalType.getAppFn;
  let fArgs := goalType.getAppArgs;
  if !(f.isConst && isClass env f.constName)
  then ({}, goalType, Array.empty, Array.empty)
  else
    let ⟨ctx, uReplacements, CLevels⟩ := collectUReplacements f.constLevels {} Array.empty Array.empty;
    let f := if uReplacements.isEmpty then f else Expr.const f.constName CLevels.toList;
    let fType :=
      match env.find f.constName with
      | none => panic! "found constant not in the environment"
      | some cInfo => cInfo.instantiateTypeUnivParams CLevels.toList;
    let (ctx, eReplacements, fArgs) := collectEReplacements env lctx locals fType fArgs ctx Array.empty Array.empty;
    (ctx, lctx.mkForall locals $ mkApp f fArgs.toList, uReplacements, eReplacements)

def synth (goalType₀ : Expr) (fuel : Nat := 100000) : TCMethod Expr :=
do env ← get >>= λ ϕ => pure ϕ.env;
   let ⟨ctx, goalType, uReplacements, eReplacements⟩ := preprocessForOutParams env goalType₀;
   ⟨instVal, instType⟩ ← synthCore ctx goalType fuel;
   match (Context.eUnify goalType₀ instType).run ctx with
   | EState.Result.error msg _ => throw $ "outParams do not match: " ++ toString goalType₀ ++ " ≠ " ++ toString instType
   | EState.Result.ok _ ctx => do
     let instVal : Expr := ctx.eInstantiate instVal;
     when (Context.eHasTmpMVar instVal) $ throw "synthesized instance has mvar";
     pure instVal

end TypeClass
end Lean
