import Lean

set_option autoImplicit true

section Mathlib.Algebra.Group.Defs

universe u v w

open Function

variable {G : Type _}

class AddMonoid (M : Type u) extends Zero M, Add M where

class Monoid (M : Type u) extends One M, Mul M where

def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : Int → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  protected zpow : Int → G → G := zpowRec
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.GroupWithZero.Defs

universe u

variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, Zero M₀

class GroupWithZero (G₀ : Type u) extends Zero G₀, DivInvMonoid G₀ where
  inv_zero : (0 : G₀)⁻¹ = 0

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Ring.Defs

universe u x

variable {α : Type u} {R : Type x}

class Semiring (α : Type u) extends NatCast α, Add α, Monoid α, Zero α

class IsDomain (α : Type u) [Semiring α] : Prop

end Mathlib.Algebra.Ring.Defs

namespace Mathlib.Elab.FastInstance

open Lean Meta Elab Term

initialize registerTraceClass `Elab.fast_instance

private partial def makeFastInstance (provided : Expr) (trace : Array Name := #[]) :
    MetaM Expr := withReducible do
  let ty ← inferType provided
  withTraceNode `Elab.fast_instance (fun e => return m!"{exceptEmoji e} type: {ty}") do
  let some className ← isClass? ty | failure
  trace[Elab.fast_instance] "class is {className}"
  if ← withDefault <| Meta.isProp ty then failure

  -- Try to synthesize a total replacement for this term:
  if let .some new ← trySynthInstance ty then
    if ← withReducibleAndInstances <| isDefEq provided new then
      trace[Elab.fast_instance] "replaced with synthesized instance"
      return new
    else
      if ← withDefault <| isDefEq provided new then failure
      else failure
  -- Otherwise, try to reduce it to a constructor.
  else
    -- Telescope since it might be a family of instances.
    forallTelescopeReducing ty fun tyArgs _ => do
      let provided' ← withReducibleAndInstances <| whnf <| mkAppN provided tyArgs
      let .const c .. := provided'.getAppFn | failure
      let some (.ctorInfo ci) := (← getEnv).find? c | failure
      let mut args := provided'.getAppArgs
      let params ← withDefault <| forallTelescopeReducing ci.type fun args _ =>
        args.mapM fun arg => do
          let recurse ← (return (← arg.fvarId!.getBinderInfo).isInstImplicit)
                        <&&> not <$> Meta.isProof arg
          return (recurse, ← arg.fvarId!.getUserName)
      unless args.size == params.size do
        -- This is an invalid term.
        throwError "Incorrect number of arguments for constructor application{indentExpr provided'}"
      for i in [ci.numParams:args.size] do
        let (recurse, binderName) := params[i]!
        if recurse then
          let trace' := trace.push (className ++ binderName)
          args := args.set! i (← makeFastInstance args[i]! (trace := trace'))
      let provided' := mkAppN provided'.getAppFn args
      mkLambdaFVars tyArgs provided'

syntax (name := fastInstance) "fast_instance%" term : term

@[term_elab fastInstance, inherit_doc fastInstance]
def elabFastInstance : TermElab
  | `(term| fast_instance%%$tk $arg), expectedType => do
    let provided ← withSynthesize <| elabTerm arg expectedType
    withRef tk do
      try
        makeFastInstance provided
      catch e =>
        logException e
        return provided
  | _, _ => Elab.throwUnsupportedSyntax

end Mathlib.Elab.FastInstance

section Mathlib.Tactic.Spread

open Lean Parser.Term Macro

syntax (name := letImplDetailStx) "let_impl_detail " ident " := " term "; " term : term

open Lean Elab Term Meta

@[term_elab letImplDetailStx, inherit_doc letImplDetailStx]
def elabLetImplDetail : TermElab := fun stx expectedType? =>
  match stx with
  | `(let_impl_detail $id := $valStx; $body) => do
    let val ← elabTerm valStx none
    let type ← inferType val
    trace[Elab.let.decl] "{id.getId} : {type} := {val}"
    let result ←
      withLetDecl id.getId (kind := .default) type val fun x => do
        addLocalVarInfo id x
        let lctx ← getLCtx
        let lctx := lctx.modifyLocalDecl x.fvarId! fun decl => decl.setKind .implDetail
        withLCtx lctx (← getLocalInstances) do
          let body ← elabTermEnsuringType body expectedType?
          let body ← instantiateMVars body
          mkLetFVars #[x] body (usedLetOnly := false)
    pure result
  | _ => throwUnsupportedSyntax

macro_rules
| `({ $[$srcs,* with]? $[$fields],* $[: $ty?]? }) => show MacroM Term from do
    let mut spreads := #[]
    let mut newFields := #[]

    for field in fields do
      match field.1 with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push arg
          else
            newFields := newFields.push field
        | _ =>
          throwUnsupported

    if spreads.isEmpty then throwUnsupported

    let spreadData ← withFreshMacroScope <| spreads.mapIdxM fun i spread => do
      let n := Name.num `__spread i
      return (mkIdent <| ← Macro.addMacroScope n, spread)

    let srcs := (srcs.map (·.getElems)).getD {} ++ spreadData.map Prod.fst
    let body ← `({ $srcs,* with $[$newFields],* $[: $ty?]? })
    spreadData.foldrM (init := body) fun (id, val) body => `(let_impl_detail $id := $val; $body)


end Mathlib.Tactic.Spread

variable {R : Type} [inst : Semiring R]

class DivisionRing (K : Type) extends Semiring K, DivInvMonoid K where
  protected inv_zero : (0 : K)⁻¹ = 0

class Field (K : Type) extends Semiring K, DivisionRing K

instance {K : Type} [inst : Field K] : Lean.Grind.Field K :=
  let r : Lean.Grind.Field K := sorry
  -- **Note**: HACK to ensure we can bypass `grind` sanity checks.
  -- The `inv` field must match the one in `
  { r with
    inv := inst.inv, div_eq_mul_inv := sorry, inv_zero := sorry, mul_inv_cancel := sorry, zpow_neg := sorry }

instance {K : Type} [Field K] : IsDomain K := sorry
instance [IsDomain R] : MonoidWithZero R := sorry
noncomputable def normalizedFactors {α : Type} [MonoidWithZero α] (a : α) : List α := sorry

structure Ideal (R : Type) [Semiring R] where
structure Ideal.Quotient (I : Ideal R) where
class Ideal.IsMaximal (I : Ideal R) : Prop where
namespace Ideal.Quotient

variable (I J : Ideal R)

instance commRing {R} [Semiring R] (I : Ideal R) : Semiring I.Quotient := sorry

protected noncomputable abbrev groupWithZero [hI : I.IsMaximal] :
    GroupWithZero (I.Quotient) :=
  { inv := sorry
    inv_zero := sorry }

protected noncomputable abbrev divisionRing [I.IsMaximal] : DivisionRing (I.Quotient) :=
  fast_instance% -- The panic seems to rely on this specific `fast_instance%`.
  { __ := commRing _
    __ := Quotient.groupWithZero _ }

protected noncomputable abbrev field {R} [Semiring R] (I : Ideal R) [I.IsMaximal] :
    Field (I.Quotient) :=
  { __ := commRing _
    __ := Quotient.divisionRing I }

end Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

open Classical in
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span.extracted_1_3
  {R : Type} [Semiring R] {I : Ideal R} [I.IsMaximal] {mapQ mapMinpoly : I.Quotient}
  (hQ : mapQ ∈ normalizedFactors mapMinpoly) :
  0 = 0 := by grind
