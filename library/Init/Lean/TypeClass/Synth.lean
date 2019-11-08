/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Typeclass synthesis using tabled resolution.

Note: this file will be need to be updated once the unifier is implemented in Lean.
-/
prelude
import Init.Lean.Expr
import Init.Lean.Environment
import Init.Lean.Class
import Init.Lean.MetavarContext
import Init.Lean.TypeClass.Context
import Init.Data.PersistentHashMap
import Init.Data.Stack
import Init.Data.Queue

namespace Lean
namespace TypeClass

structure TypedExpr : Type :=
(val type : Expr)

instance TypedExpr.HasToString : HasToString TypedExpr :=
⟨λ ⟨val, type⟩ => "TypedExpr(" ++ toString val ++ ", " ++ toString type ++ ")"⟩

instance TypedExpr.Inhabited : Inhabited TypedExpr :=
⟨⟨arbitrary _, arbitrary _⟩⟩

structure Answer : Type :=
(ctx : Context) (typedExpr : TypedExpr)

instance Answer.HasToString : HasToString Answer :=
⟨λ ⟨_, ⟨val, type⟩⟩ => "Answer(" ++ toString val ++ ", " ++ toString type ++ ")"⟩

instance Answer.Inhabited : Inhabited TypedExpr :=
⟨⟨arbitrary _, arbitrary _⟩⟩

structure Node : Type :=
(anormSubgoal : Expr)
(ctx          : Context)
(futureAnswer : TypedExpr)

instance Node.Inhabited : Inhabited Node :=
⟨⟨arbitrary _, {}, arbitrary _⟩⟩

structure ConsumerNode extends Node :=
(remainingSubgoals : List Expr)

instance ConsumerNode.Inhabited : Inhabited ConsumerNode :=
⟨⟨arbitrary _, arbitrary _⟩⟩

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
⟨⟨arbitrary _, arbitrary _⟩⟩

structure TableEntry : Type :=
(waiters    : Array Waiter)
(answers    : Array Answer := #[])

structure TCState : Type :=
(env            : Environment)
(finalAnswer    : Option TypedExpr                  := none)
(mainMVar       : Expr                              := arbitrary _)
(generatorStack : Stack GeneratorNode               := Stack.empty)
(consumerStack  : Stack ConsumerNode                := Stack.empty)
(resumeQueue    : Queue (ConsumerNode × Answer)     := Queue.empty)
(tableEntries   : PersistentHashMap Expr TableEntry := PersistentHashMap.empty)

abbrev TCMethod : Type → Type := EStateM String TCState

-- TODO(dselsam): once `whnf` is ready, need a more expensive pass as a backup,
-- that creates locals and calls `whnf` on every recursion.
-- See: [type_context.cpp] optional<name> type_context_old::is_full_class(expr type)
-- TODO(dselsam): check if we need to call `get_decl()` as well in the `const` case.
def quickIsClass (env : Environment) : Expr → Option (Option Name)
| Expr.letE _ _ _ _    => none
| Expr.proj _ _ _      => none
| Expr.mdata _ e       => quickIsClass e
| Expr.const n _       => if isClass env n then some (some  n) else none
| Expr.forallE _ _ _ b => quickIsClass b
| Expr.app e _         =>
  let f := e.getAppFn;
  if f.isConst && isClass env f.constName! then some (some f.constName!)
  else if f.isLambda then none
  else some none
| _            => some none

def newSubgoal (waiter : Waiter) (ctx : Context) (anormSubgoal mvar : Expr) : TCMethod Unit :=
do let mvarType := ctx.eInfer mvar;
   isClassStatus ← get >>= λ ϕ => pure $ quickIsClass ϕ.env mvarType;
   match isClassStatus with
   | none      => throw $ "quickIsClass not sufficient to show `" ++ toString mvarType ++ "` is a class"
   | some none => throw $ "found non-class goal `" ++ toString mvarType ++ "`"
   | some (some n) => do
     gNode ← get >>= λ ϕ => pure {
       GeneratorNode .
       ctx                := ctx,
       anormSubgoal       := anormSubgoal,
       futureAnswer       := ⟨mvar, mvarType⟩,
       remainingInstances := (getClassInstances ϕ.env n).map Instance.const
     };
     let tableEntry : TableEntry := { waiters := #[waiter] };
     modify $ λ ϕ => {
       generatorStack := ϕ.generatorStack.push gNode,
       tableEntries   := ϕ.tableEntries.insert gNode.anormSubgoal tableEntry,
       .. ϕ
     }

partial def introduceMVars (lctx : LocalContext) (locals : Array Expr) : Context → Expr → Expr → Array Expr → Context × Expr × Expr × Array Expr
| ctx, instVal, Expr.forallE _ info domain body, mvars => do
  let ⟨mvar, ctx⟩ := (Context.eNewMeta $ lctx.mkForall locals domain).run ctx;
  let arg := mkApp mvar locals;
  let instVal := Expr.app instVal arg;
  let instType := body.instantiate1 arg;
  let mvars := if info.isInstImplicit then mvars.push mvar else mvars;
  introduceMVars ctx instVal instType mvars

| ctx, instVal, instType, mvars => (ctx, instVal, instType, mvars)

partial def introduceLocals : Nat → LocalContext → Array Expr → Expr → LocalContext × Expr × Array Expr
| nextIdx, lctx, ls, Expr.forallE name info domain body =>
  let idxName : Name := mkNumName (mkSimpleName "_tmp") nextIdx;
  let lctx := lctx.mkLocalDecl idxName name domain info;
  let l : Expr := Expr.fvar idxName;
  introduceLocals (nextIdx + 1) lctx (ls.push l) (body.instantiate1 l)

| _, lctx, ls, e => (lctx, e, ls)

def tryResolve (ctx : Context) (futureAnswer : TypedExpr) (instTE : TypedExpr) : TCMethod (Option (Context × List Expr)) :=
do let ⟨mvar, mvarType⟩ := futureAnswer;
   let ⟨instVal, instType⟩ := instTE;
   let ⟨lctx, mvarType, locals⟩ := introduceLocals 0 {} #[] mvarType;
   let ⟨ctx, instVal, instType, newMVars⟩ := introduceMVars lctx locals ctx instVal instType #[];
   match (Context.eUnify mvarType instType *> Context.eUnify mvar (lctx.mkLambda locals instVal)).run ctx with
   | EStateM.Result.error msg   _ => pure none
   | EStateM.Result.ok    _   ctx => pure $ some $ (ctx, newMVars.toList) -- TODO(dselsam): rm toList

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
     let newCtx : Context := cNode.ctx;
     let ⟨newVal, newType, newCtx⟩ : Expr × Expr × Context := Context.internalize answer.ctx answer.typedExpr.val answer.typedExpr.type newCtx;
     result : Option (Context × List Expr) ←
       tryResolve newCtx ⟨mvar, newCtx.eInfer mvar⟩ ⟨newVal, newType⟩;
     modify $ λ ϕ => { resumeQueue := resumeQueue, .. ϕ };
     match result with
     | none => pure ()
     | some (newCtx, newMVars) => newConsumerNode cNode.toNode newCtx (newMVars ++ rest)

def wakeUp (answer : Answer) : Waiter → TCMethod Unit
| Waiter.root               => modify $ λ ϕ => { finalAnswer := some answer.typedExpr .. ϕ }
| Waiter.consumerNode cNode => modify $ λ ϕ => { resumeQueue := ϕ.resumeQueue.enqueue (cNode, answer), .. ϕ }

def newAnswer (anormSubgoal : Expr) (answer : Answer) : TCMethod Unit :=
do lookupStatus ← get >>= λ ϕ => pure $ ϕ.tableEntries.find anormSubgoal;
   match lookupStatus with
   | none       => throw $ "[newAnswer]: " ++ toString anormSubgoal ++ " not found in table!"
   | some entry => do
     -- TODO(dselsam): avoid alpha-normalizing the value (type is okay)
     -- Could check if Waiter.root is in the queue, and if so reject the answer if it contains metavars.
     if entry.answers.any (λ answer₁ => Context.αNorm (answer₁.typedExpr.type) == Context.αNorm (answer.typedExpr.type)
                                     && Context.αNorm (answer₁.typedExpr.val) == Context.αNorm (answer.typedExpr.val)) then pure() else do
       let newEntry : TableEntry := { answers := entry.answers.push answer .. entry };
       modify $ λ ϕ => { tableEntries := ϕ.tableEntries.insert anormSubgoal newEntry .. ϕ };
       entry.waiters.forM (wakeUp answer)

def consume : TCMethod Unit :=
do cNode ← get >>= λ ϕ => pure ϕ.consumerStack.peek!;
   modify $ λ ϕ => { consumerStack := ϕ.consumerStack.pop .. ϕ };
   match cNode.remainingSubgoals with
   | [] => do
     let answer : Answer := {
       ctx := cNode.ctx,
       typedExpr := {
         val  := cNode.ctx.eInstantiate cNode.futureAnswer.val,
         type := cNode.ctx.eInstantiate cNode.futureAnswer.type
     }};
     newAnswer cNode.anormSubgoal answer

   | mvar::rest => do
     let anormSubgoal : Expr := Context.αNorm (cNode.ctx.eInstantiate $ cNode.ctx.eInfer mvar);
     let waiter : Waiter := Waiter.consumerNode cNode;
     lookupStatus ← get >>= λ ϕ => pure $ ϕ.tableEntries.find anormSubgoal;
     match lookupStatus with
     | none => newSubgoal waiter cNode.ctx anormSubgoal mvar
     | some entry => modify $ λ ϕ => {
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
     let instType      := cInfo.instantiateTypeLevelParams uMetas;
     pure ⟨⟨instVal, instType⟩, ctx⟩

def generate : TCMethod Unit :=
do gNode ← get >>= λ ϕ => pure ϕ.generatorStack.peek!;
   match gNode.remainingInstances with
   | []          => modify $ λ ϕ => { generatorStack := ϕ.generatorStack.pop, .. ϕ }
   | inst::insts => do
     ⟨instTE, ctx⟩ ← match inst with
                     | Instance.const n     => constNameToTypedExpr gNode.ctx n
                     | Instance.lDecl lDecl => throw "local instances not yet supported";
     result : Option (Context × List Expr) ← tryResolve ctx gNode.futureAnswer instTE;
     modify $ λ ϕ => { generatorStack := ϕ.generatorStack.modify (λ gNode => { remainingInstances := insts .. gNode }) .. ϕ };
     match result with
     | none => pure ()
     | some (ctx, newMVars) => newConsumerNode gNode.toNode ctx newMVars

def step : TCMethod Unit :=
do ϕ ← get;
   if !ϕ.resumeQueue.isEmpty then resume
   else if !ϕ.consumerStack.isEmpty then consume
   else if !ϕ.generatorStack.isEmpty then generate
   else throw "FAILED TO SYNTHESIZE"

partial def synthCore (ctx₀ : Context) (goalType : Expr) : Nat → TCMethod TypedExpr
| 0   => throw "[synthCore] out of fuel"
| n+1 => do
  step;
  finalAnswer ← get >>= λ ϕ => pure ϕ.finalAnswer;
  match finalAnswer with
  | none => synthCore n
  | some ⟨answerVal, answerType⟩ =>
    if Context.eHasTmpMVar answerVal || Context.eHasTmpMVar answerType then do
      modify $ λ ϕ => { finalAnswer := none, .. ϕ };
      synthCore n
    else
      pure ⟨answerVal, answerType⟩

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

| Expr.forallE _ _ d b, arg::args, ctx, eReplacements, fArgs =>
  if isOutParam d then
    let ⟨eMeta, ctx⟩ := (Context.eNewMeta $ lctx.mkForall locals d).run ctx;
    let fArg : Expr  := mkApp eMeta locals;
    collectEReplacements (b.instantiate1 fArg) args ctx (eReplacements.push (eMeta, arg)) (fArgs.push fArg)
  else
    collectEReplacements (b.instantiate1 arg) args ctx eReplacements (fArgs.push arg)

| _, arg::args, _, _, _ => panic! "TODO(dselsam): this case not yet handled"

def preprocessForOutParams (env : Environment) (goalType : Expr) : Context × Expr × Array (Level × Level) × Array (Expr × Expr) :=
if !goalType.hasMVar && goalType.getAppFn.isConst && !hasOutParams env goalType.getAppFn.constName!
then ({}, goalType, #[], #[])
else
  let ⟨lctx, bodyGoalType, locals⟩ := introduceLocals 0 {} #[] goalType;
  let f := goalType.getAppFn;
  let fArgs := goalType.getAppArgs;
  if !(f.isConst && isClass env f.constName!)
  then ({}, goalType, #[], #[])
  else
    let ⟨ctx, uReplacements, CLevels⟩ := collectUReplacements f.constLevels! {} #[] #[];
    let f := if uReplacements.isEmpty then f else Expr.const f.constName! CLevels.toList;
    let fType :=
      match env.find f.constName! with
      | none => panic! "found constant not in the environment"
      | some cInfo => cInfo.instantiateTypeLevelParams CLevels.toList;
    let (ctx, eReplacements, fArgs) := collectEReplacements env lctx locals fType fArgs.toList ctx #[] #[]; -- TODO: avoid fArgs.toList
    (ctx, lctx.mkForall locals $ mkApp f fArgs, uReplacements, eReplacements)

def synth (goalType₀ : Expr) (fuel : Nat := 100000) : TCMethod Expr :=
do env ← get >>= λ ϕ => pure ϕ.env;
   let ⟨ctx₀, goalType, uReplacements, eReplacements⟩ := preprocessForOutParams env goalType₀;
   let ⟨mvar, ctx⟩ := (Context.eNewMeta goalType).run ctx₀;
   let anormSubgoal : Expr := Context.αNorm goalType;
   newSubgoal Waiter.root ctx anormSubgoal mvar;
   modify $ λ ϕ => { mainMVar := mvar .. ϕ };
   ⟨instVal, instType⟩ ← synthCore ctx₀ goalType fuel;
   match (Context.eUnify goalType₀ instType).run ctx with
   | EStateM.Result.error msg _ => throw $ "outParams do not match: " ++ toString goalType₀ ++ " ≠ " ++ toString instType
   | EStateM.Result.ok _ ctx => do
     let instVal : Expr := ctx.eInstantiate instVal;
     when (Context.eHasTmpMVar instVal) $ throw "synthesized instance has mvar";
     pure instVal

end TypeClass
end Lean
