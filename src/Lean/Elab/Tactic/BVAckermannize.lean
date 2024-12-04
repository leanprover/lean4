/-
Copyright (c) 2024 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file implements strict ackermannization [1, 2]

[1] https://lara.epfl.ch/w/_media/model-based.pdf
[2] https://leodemoura.github.io/files/oregon08.pdf
[3] https://github.com/Z3Prover/z3/blob/d047b86439ec209446d211f0f6b251ebfba070d8/src/ackermannization/lackr.cpp#L206
[4] https://github.com/Z3Prover/z3/blob/d047b86439ec209446d211f0f6b251ebfba070d8/src/ackermannization/lackr_model_constructor.cpp#L344
-/
prelude
import Lean.Expr
import Lean.Message
import Std.Tactic.BVDecide.Bitblast
import Std.Tactic.BVAckermannize.Syntax
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic
import Lean.Meta.LitValues
import Lean.Meta.InferType
import Lean.Elab.Tactic.FalseOrByContra
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Congr
import Lean.Meta.Tactic.Replace

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `Meta.Tactic.bv_ack

namespace Ack

 /-- Types that can be bitblasted by bv_decide. -/
 inductive BVTy
   /-- Booleans. -/
   | Bool
   /-- Bitvectors of a fixed width `w`. -/
   | BitVec (w : Nat)
   deriving Hashable, DecidableEq, Inhabited

instance : ToMessageData BVTy where
  toMessageData
  | .Bool => m!"bool"
  | .BitVec w => m!"BitVec {w}"

namespace BVTy

/-- Reify a raw expression of type `Type` into the types of bitvectors we can bitblast,
returning `none` if `e` was not recognized as either `Bool` or `BitVec ?w`,
with `?w` a literal `Nat`.  -/
def ofExpr? (e : Expr) : MetaM (Option BVTy) := ofExpr?Aux e |>.run where
  ofExpr?Aux (e : Expr) : OptionT MetaM BVTy :=
    match_expr e.consumeMData with
    | _root_.Bool => return Bool
    | _root_.BitVec w => do
       let w ← getNatValue? w
       return .BitVec w
    | _ => OptionT.fail

/-- Convert a `BVTy` back into an `Expr`. -/
def toExpr : BVTy → Expr
| .Bool => mkConst ``_root_.Bool
| .BitVec w => mkApp (mkConst ``_root_.BitVec) (mkNatLit w)

end BVTy

/-- An argument to an uninterpreted function, which we track for ackermannization. -/
structure Argument where
  /-- The expression corresponding to the argument. -/
  value : Expr
  /-- The type of the argument. -/
  type : BVTy
deriving Hashable, BEq, Inhabited

namespace Argument

instance : ToMessageData Argument where
  toMessageData arg := m!"{arg.value}"
end Argument

/--
A function, which packs the expression and the type of the codomain.
We use the type of the codomain to build an abstracted value for every call of this function.
-/
structure Function where
  /-- The function -/
  f : Expr
  /-- The type of the function's codomain -/
  codomain : BVTy
 deriving Hashable, BEq, Inhabited

namespace Function

instance : ToMessageData Function where
  toMessageData fn := m!"{fn.f} (cod: {fn.codomain})"

end Function

/--
NOTE: is it sensible to hash an array of arguments?
We may want to use something like a trie to index these.
Consider swiching to something like `Trie`.
-/
abbrev ArgumentArray := Array Argument

/-- The data stored for an ackermannized call to allow us to build proofs. -/
structure CallInfo where
  /-- The free variable `ack_fx₁...xₙ := (f x₁ x₂ ... xₙ)`. -/
  fvar : FVarId
  /-- heqProof : The proof that `ack_fx₁...fxₙ = f x₁ x₂ ... xₙ` (name/fvar = value/expr). -/
  heqProof : Expr
deriving Hashable, BEq, Inhabited

namespace CallInfo

instance : ToMessageData CallInfo where
  toMessageData cv := m!"{Expr.fvar cv.fvar} ({cv.heqProof})"

end CallInfo
structure State where
  /--
  A mapping from a function `f`, to a map of arguments `x₁ ... xₙ`, to the information stored about the call.
  This is used to generate equations of the form `x₁ = y₁ → x₂ = y₂ → ... → xₙ = yₙ → ack_fx₁...xₙ = ack_fy₁...yₙ.
  -/
  fn2args2call : Std.HashMap Function (Std.HashMap ArgumentArray CallInfo) := {}
  /-- A counter for generating fresh names. -/
  gensymCounter : Nat := 0

def State.init : State where

abbrev AckM := StateRefT State MetaM

namespace AckM

def run (m : AckM α) : MetaM α := m.run' State.init

/-- Generate a fresh name. -/
def gensym : AckM Name := do
  modify fun s => { s with gensymCounter := s.gensymCounter + 1 }
  return Name.mkNum (Name.mkSimple "ackConst") (← get).gensymCounter

def withContext (g : MVarId) (ma : AckM α) : AckM α := g.withContext ma

/-- Get the map from an argument list to a call of a function `fn`. -/
def _getCallMap (fn : Function) : AckM (Std.HashMap ArgumentArray CallInfo) := do
  return (← get).fn2args2call.getD fn {}

/-- Get the calls to a function `fn`. -/
def getCallVal? (fn : Function) (args : Array Argument) : AckM (Option CallInfo) := do
  return (← _getCallMap fn).get? args

structure IntroDefResult where
  -- the new name/fvar of the defn.
  defn : FVarId
  -- a proof 'hdefn : name = value
  eqProof : FVarId

/-
Introduce a new definition with name `name : hdefTy` into the local context,
and return the FVarId of the new definition in the new goal (the MVarId) returned.
-/
def introDefExt (g : MVarId) (name : Name) (hdefTy : Expr) (hdefVal : Expr) : AckM (IntroDefResult × MVarId) := do
  withContext g do
    let g ← g.assertExt name (hName := Name.str name "value") hdefTy hdefVal
    let (defn, g) ← g.intro1P
    let (eqProof, g) ← g.intro1P
    return ({ defn, eqProof}, g)

/-- Insert the CallInfo `cv` at `(fn, args)` into the state. -/
private def _insertCallVal (fn : Function) (args : ArgumentArray) (cv : CallInfo) : AckM Unit := do
  let calls ← _getCallMap fn
  modify fun s => { s with fn2args2call := s.fn2args2call.insert fn (calls.insert args cv) }

/--
Replace a call `f x₁ ... xₙ` with a new free variable `fv` where `fv := f x₁ ... xₙ`.
This free variable `fv` is cached, and represented by a `CallVal`.
Moreover, Since the `fv` is defeq to `f x₁ ... xₙ, we can substitute `fv` for `f x₁ ... xₙ`.
-/
def insertOrLookupCall (g : MVarId) (fn : Function) (args : ArgumentArray) : AckM (CallInfo × MVarId) := do
  g.withContext do
    if let some val ← getCallVal? fn args then
      trace[Meta.Tactic.bv_ack] "using cached call {val} for {fn} {args}"
      return (val, g)
    let e := mkAppN fn.f (args.map Argument.value)
    let name ← gensym
    let (introDef, g) ← introDefExt g name fn.codomain.toExpr e
    let cv := { fvar := introDef.defn, heqProof := Expr.fvar introDef.eqProof : CallInfo }
    _insertCallVal fn args cv
    return (cv, g)

/-- Create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def withTraceNode (g : MVarId) (header : MessageData) (k : AckM α)
    (collapsed : Bool := true)
    (traceClass : Name := `Meta.Tactic.bv_ack) : AckM α :=
  withContext g do Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

/--
The result of running ackermannization on an expression. Returns the ackermannized expression,
as well as informing whether this expression can be used as a subexpression for further ackermannization,
by tracking whether the expression has loose bound variables.
-/
structure AckResult where
  /-- The resulting expression from ackermannization. -/
  val : Expr
  /--
  Whether an expression has bound variables in it.
  If it does, then it cannot be used as the subexpression of an ackermanized call,
  since the expression is not zeroth-order.
  -/
  hasLooseBvar : Bool
deriving Inhabited


/--
Given a binary effectful computation `f : α → β → m γ`, and two arrays `as : Array α` and `bs : Array β`,
build an array whose elements are created by invoking `f as[i] bs[i]` in sequence.
This obeys the equation `zipWithM as bs f = as.zip bs |>.mapM f
-/
private def _root_.Array.zipWithM [Monad m] (as : Array α) (bs : Array β) (f : α → β → m γ) : m (Array γ) := do
  let mut out := #[]
  for (a, b) in as.zip bs do
    out := out.push (← f a b)
  return out

mutual

/--
Try to ackermannize an application. Recursively ackermannize all of its subexpressions,
and try to ackermannize the application if:
- Neither the function `f` nor the arguments `x₁` ... `xₙ` have bound variables in them.
- `f` has a type that is ackermannizable: all arguments and output are either `BitVec w` or `Bool`.
-/
partial def ackApp (g : MVarId) (app : Expr) : AckM (AckResult × MVarId) := do
  g.withContext do
    let f := app.getAppFn
    let (f, g) ← introAckForExpr g f
    let mut hasLooseBvar := f.hasLooseBvar
    let mut args : Array Expr := #[]
    let mut g := g

    for arg in app.getAppArgs do
      let (out, g') ← g.withContext do introAckForExpr g arg
      g := g'
      args := args.push out.val
      hasLooseBvar := hasLooseBvar || out.hasLooseBvar
      -- If we have loose bvars, then we give up on ackermannizing.
      if hasLooseBvar then continue
    -- `nonAckRet` is the return value in case we fail to ackermannize the call.
    let nonAckRet := ({ val := mkAppN f.val args, hasLooseBvar }, g)
    -- We have loose bvars, so bail out.
    if hasLooseBvar then return nonAckRet
    
    -- We know that we have no loose bvars, so it's legal to call inferType.
    let resultType ← inferType app
    let some codomain ← g.withContext do BVTy.ofExpr? resultType | return nonAckRet
    -- The function is ackermanizable.
    let ackFn := { f := f.val, codomain : Function }
    -- If all our arguments were legal ackermannization arguments, then
    -- we can ackermannize. If not, we bail out.
    let mut ackArgs := #[]
    for arg in args do
      -- We know that we have no loose bvars, so it's legal to call inferType.
      -- Check if the type is a bitvector type.
      let some ty ← g.withContext do BVTy.ofExpr? (← inferType arg) | return nonAckRet
      ackArgs := ackArgs.push <| Argument.mk arg ty
    -- ackermannize our call.
    let (call, g') ← g.withContext do insertOrLookupCall g ackFn ackArgs
    g := g'
    withContext g do trace[Meta.Tactic.bv_ack] "{checkEmoji} {app} → {call}."
    let val := Expr.fvar call.fvar
    return ({ val, hasLooseBvar := false }, g)

/--
Traverse the expression 'e', and ackermannize potential subexpressions.
We explicitly do not want to use `forallTelescoping` and family,
because we want to only work with the zeroth order fragment (predicate logic),
and ignore anything that is first (and higher) order.

Hence, we use an `AckResult`, which keeps track of whether the resulting
expression has a loose bvar.

If the expression `e` is an application `f x₁ ... xₙ`, and none of `f`, `x₁`, ..., `xₙ`
have loose bvars, we try to ackermannize at `ackApp`.
If the application does have a bvar, we do not ackermannize.

This invariant is maintained by `ackApp`, and `introAckForExpr` visits
expressions and ackermannizes them in turn.
-/

partial def introAckForExpr (g : MVarId) (e : Expr) : AckM (AckResult × MVarId) :=
  withContext g do
    withTraceNode g (m!"🎯 {e}") (collapsed := false) do
    match e with
    | .mdata _ e => introAckForExpr g e
    | .bvar _ => return ({ val := e, hasLooseBvar := true }, g)
    | .proj tyName struct e =>
      let (out, g) ← introAckForExpr g e
      return ({ val := .proj tyName struct out.val, hasLooseBvar := out.hasLooseBvar}, g)
    | .fvar .. | .mvar .. | .sort .. | .const .. |  .lit .. => do
      return ({ val := e, hasLooseBvar := false }, g)
    | .lam _binderName binderTy body _binderInfo =>
        let (binderTy, g) ← introAckForExpr g binderTy
        let (body, g) ← introAckForExpr g body
        let val := e.updateLambdaE! binderTy.val body.val
        let hasLooseBvar := binderTy.hasLooseBvar || body.hasLooseBvar
        return ({ val, hasLooseBvar}, g)
    | .letE _declName type value body _nonDep =>
        let (type, g) ← introAckForExpr g type
        let (value, g) ← introAckForExpr g value
        let (body, g) ← introAckForExpr g body
        let val := e.updateLet! type.val value.val body.val
        let hasLooseBvar := type.hasLooseBvar || value.hasLooseBvar || body.hasLooseBvar
        return ({ val, hasLooseBvar}, g)
    | .forallE _binderName binderTy body _binderInfo =>
        let (binderTy, g) ← introAckForExpr g binderTy
        let (body, g) ← introAckForExpr g body
        let val := e.updateForallE! binderTy.val body.val
        let hasLooseBvar := binderTy.hasLooseBvar || body.hasLooseBvar
        return ({ val, hasLooseBvar}, g)
    | .app .. => withTraceNode g m!"🎯 Expr.app '{e}'" (collapsed := false) do
      ackApp g e
end

/--
Return true if the argument lists are trivially different.
This is an optimization that we do not yet implement.
-/
def areArgListsTriviallyDifferent (_arg₁ _arg₂ : Array Argument) : AckM Bool := return false

/-
Return true if the argument lists are trivially the same.
This is an optimization that we do not yet implement.
If possible, return the simplified hypothesis of the equality of these expressions.
TODO: -- def areArgListsTriviallySame (arg₁ arg₂ : Array Argument) : AckM (Option Expr) := return none
-/


/-- info: congr.{u, v} {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ -/
#guard_msgs in #check congr

/-- This is how we build the congruence lemma for `n` arguments. -/
private example (f : X1 → X2 → O)
    -- we have these already.
    (x1 x1' : X1) (x2 x2' : X2)
    (ackEqApp : fx1x2 = f x1 x2)
    (ackEqApp' : fx1'x2' = f x1' x2')
    -- to be intros'd
    (h1 : x1 = x1')
    (h2 : x2 = x2') :
  fx1x2 = fx1'x2' :=
  let appEqApp : f x1 x2 = f x1' x2' := congr (congr (Eq.refl f) h1) h2
  Eq.trans (Eq.trans ackEqApp appEqApp) (Eq.symm ackEqApp')

/--
Make the ackermannization theorem, which states that: `(∀ i, arg₁[i] = arg₂[i]) -> call₁ = call₂`.
Formally, we build an expr such as `arg₁ = arg'₁ -> arg₂ = arg'₂ -> ... argₙ = arg'ₙ -> call₁ = call₂`,
where the proof is by congruence over the equalities.
-/
def mkAckThm (g : MVarId) (fn : Function) (args args' : Array Argument) (call call' : CallInfo) : AckM MVarId := do
  withContext g do
    trace[Meta.Tactic.bv_ack] "making ack congr thm for '{fn}' '{args}' ~ '{args'}',  calls '{call}', '{call'}'"
    if args.size = 0 then
      throwTacticEx `bv_ack g
        m!"expected {args} to have more than zero arguments when building congr theorem for {fn}."
    if args'.size = 0 then
      throwTacticEx `bv_ack g
        m!"expected {args'} to have more than zero arguments when building congr theorem for {fn}."

    if args.size ≠ args'.size then
      throwTacticEx `bv_ack g
        m!"internal error: expected {args} to have the same size as {args'} when building congr thm for {fn}."

    let mut eqHyps := #[]
    for (arg, arg') in args.zip args' do
      eqHyps := eqHyps.push (← mkEq arg.value arg'.value)
    -- we build the equality according to the example above.
    let mut localDecls : Array (Name × BinderInfo × (Array Expr → AckM Expr)) := #[]
    let mut i := 0
    for (arg, arg') in args.zip args' do
      let name := Name.num (Name.mkSimple "ack_arg") i
      localDecls := localDecls.push (name, BinderInfo.default, fun _ => mkEq arg.value arg'.value)
    let ackEqn ← g.withContext <| withLocalDecls localDecls fun argsEq => do
      let mut fEq ← mkEqRefl fn.f
      for argEq in argsEq do
        fEq ← mkCongr fEq argEq

      let finalEq ← mkEqTrans (← mkEqTrans call.heqProof fEq) (← mkEqSymm call'.heqProof)
      mkLambdaFVars argsEq  finalEq
    withContext g do trace[Meta.Tactic.bv_ack] "made ackermann equation: {ackEqn}"
    let (_ackEqn, g) ← g.note (Name.mkSimple s!"ackEqn{fn.f}") ackEqn
    return g

/--
For every bitvector (x : BitVec w), for every function `(f : BitVec w → BitVec w')`,
walk every function application (f x), and add a new fvar (fx : BitVec w').
- Keep an equality that says `fx = f x`.
- For function application of f, for each pair of bitvectors x, y,
  add a hypothesis that says `x = y => fx = fy, with proof.

FUTUREWORK: This can be extended to work with functions where only the output type is bitblastable,
so this will allow us to ackemannize equations such as `f : Nat → BitVec w → BitVec w`, with `(f 0) x` and `(f 0) y`
being correctly handled. That is, we can add the equation `x = y → f 0 x = f 0 y`.
-/
def ack (g : MVarId) : AckM MVarId := do
  g.withContext do
    let target ← g.getType
    let (target', g) ← introAckForExpr g (← g.getType)
    let g ← g.replaceTargetDefEq target'.val
    let hyps ← g.getNondepPropHyps

    let mut g := g
    for hyp in hyps do
      g ← g.withContext do
        withTraceNode g m!"🎯 hyp '{← hyp.getType}'" (collapsed := false) do
          let (_hyp, g) ← introAckForExpr g (← hyp.getType)
          pure g

    for (fn, arg2call) in (← get).fn2args2call do
      let argCallsArr := arg2call.toArray
      for hi : i in [0:argCallsArr.size] do
        let (arg₁, call₁) := argCallsArr[i]
        for hj : j in [i+1:argCallsArr.size] do
          let (arg₂, call₂) := argCallsArr[j]
          if ← areArgListsTriviallyDifferent arg₁ arg₂ then continue
          g ← mkAckThm g fn arg₁ arg₂ call₁ call₂
    withContext g do trace[Meta.Tactic.bv_ack] "{checkEmoji} ack.{indentD g}"
    return g

end AckM

/-- Entry point for programmatic usage of `bv_ackermannize`. -/
def ackTac : TacticM Unit := do
  withoutRecover do
    liftMetaTactic fun g => do
      let g ← (AckM.ack g).run
      return [g]

end Ack

@[builtin_tactic Lean.Parser.Tactic.bvAckEager]
def evalBvAckEager : Tactic := fun
  | `(tactic| bv_ack_eager) =>
    Ack.ackTac
  | _ => throwUnsupportedSyntax
