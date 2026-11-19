import Lean

/-!
# Named-binder reification of a higher-order SMT-LIB fragment with `expr` quotations

Lean terms over `Bool`, `Int` and functions are reified into `NExpr`, an untyped SMT-LIB 2.7
syntax with `String`-named binders (`lambda`, `let`) and variables. The decidable typechecker
`infer` elaborates it into the intrinsically typed `Exp : Ctx → SmtSort → Type`, whose `Lookup`
resolves names with lexical shadowing (`here` on a name match, `there (h : x ≠ y)` otherwise),
so `Exp.eval` needs no fuel. `Exp.opt` is a verified optimizer, and `named_reflect` proves
equations by reflection, with free context variables acting as `declare-fun` symbols.

The reifier tracks `FVarId ↦ String` and the names in scope (`usedNames`). Binder names lose
their macro scopes; a binder keeps its user name (shadowing outer ones) unless its body mentions
a live local of that name, in which case it is renamed to avoid capture.
-/

namespace ExprQuotReifyNamed
open Lean Meta Elab Tactic

/-- SMT-LIB sorts `Bool`, `Int` and `(-> σ τ)`. -/
inductive SmtSort where
  | bool | int | arr (dom cod : SmtSort)
  deriving DecidableEq, ToExpr

@[reducible] def SmtSort.denote : SmtSort → Type
  | .bool => Bool | .int => Int | .arr a b => a.denote → b.denote

def SmtSort.toSmtLib : SmtSort → String
  | .bool => "Bool" | .int => "Int" | .arr a b => s!"(-> {a.toSmtLib} {b.toSmtLib})"

/-! ## Typed named syntax -/

abbrev Ctx := List (String × SmtSort)

/-- Lexically scoped resolution of name `x` at sort `s`. -/
inductive Lookup : Ctx → String → SmtSort → Type where
  | here : Lookup ((x, s) :: Γ) x s
  | there : x ≠ y → Lookup Γ x s → Lookup ((y, t) :: Γ) x s

inductive Exp : Ctx → SmtSort → Type where
  | var : Lookup Γ x s → Exp Γ s
  | boolLit : Bool → Exp Γ .bool
  | intLit : Int → Exp Γ .int
  | not : Exp Γ .bool → Exp Γ .bool
  | ite : Exp Γ .bool → Exp Γ s → Exp Γ s → Exp Γ s
  | eq : Exp Γ .int → Exp Γ .int → Exp Γ .bool
  | add : Exp Γ .int → Exp Γ .int → Exp Γ .int
  | lam (x : String) (a : SmtSort) : Exp ((x, a) :: Γ) b → Exp Γ (.arr a b)
  | app : Exp Γ (.arr a b) → Exp Γ a → Exp Γ b
  | let_ (x : String) : Exp Γ a → Exp ((x, a) :: Γ) b → Exp Γ b

inductive Env : Ctx → Type where
  | nil : Env []
  | cons : s.denote → Env Γ → Env ((x, s) :: Γ)

def Lookup.get : Lookup Γ x s → Env Γ → s.denote
  | .here, .cons v _ => v
  | .there _ l, .cons _ ρ => l.get ρ

def Exp.eval : Exp Γ s → Env Γ → s.denote
  | .var l, ρ => l.get ρ
  | .boolLit b, _ | .intLit b, _ => b
  | .not b, ρ => !b.eval ρ
  | .ite c x y, ρ => if c.eval ρ then x.eval ρ else y.eval ρ
  | .eq a b, ρ => a.eval ρ == b.eval ρ
  | .add a b, ρ => a.eval ρ + b.eval ρ
  | .lam _ _ b, ρ => fun v => b.eval (.cons v ρ)
  | .app f a, ρ => f.eval ρ (a.eval ρ)
  | .let_ _ a b, ρ => b.eval (.cons (a.eval ρ) ρ)

/-! ## Untyped named syntax and typechecker -/

inductive NExpr where
  | var (x : String) | boolLit (b : Bool) | intLit (i : Int) | not (b : NExpr)
  | ite (c x y : NExpr) | eq (a b : NExpr) | add (a b : NExpr)
  | lam (x : String) (s : SmtSort) (body : NExpr) | app (f a : NExpr)
  | let_ (x : String) (v body : NExpr)
  deriving ToExpr

def NExpr.toSmtLib : NExpr → String
  | .var x => x | .boolLit b => toString b | .intLit i => toString i
  | .not b => s!"(not {b.toSmtLib})"
  | .ite c x y => s!"(ite {c.toSmtLib} {x.toSmtLib} {y.toSmtLib})"
  | .eq a b => s!"(= {a.toSmtLib} {b.toSmtLib})"
  | .add a b => s!"(+ {a.toSmtLib} {b.toSmtLib})"
  | .lam x s b => s!"(lambda (({x} {s.toSmtLib})) {b.toSmtLib})"
  | .app f a => s!"(@ {f.toSmtLib} {a.toSmtLib})"
  | .let_ x v b => s!"(let (({x} {v.toSmtLib})) {b.toSmtLib})"

def lookup : (Γ : Ctx) → (x : String) → Option (Σ s, Lookup Γ x s)
  | [], _ => none
  | (y, t) :: Γ, x =>
    if h : x = y then some ⟨t, h ▸ .here⟩ else (lookup Γ x).map fun ⟨s, l⟩ => ⟨s, .there h l⟩

def castTo : (Σ s', Exp Γ s') → (s : SmtSort) → Option (Exp Γ s)
  | ⟨s', e⟩, s => if h : s' = s then some (h ▸ e) else none

/-- Sort inference; binders are annotated, so every sort is synthesized. -/
def infer : (Γ : Ctx) → NExpr → Option (Σ s, Exp Γ s)
  | Γ, .var x => (lookup Γ x).map fun ⟨s, l⟩ => ⟨s, .var l⟩
  | _, .boolLit b => some ⟨.bool, .boolLit b⟩
  | _, .intLit i => some ⟨.int, .intLit i⟩
  | Γ, .not b => do return ⟨.bool, .not (← (infer Γ b).bind (castTo · .bool))⟩
  | Γ, .ite c x y => do
    let c ← (infer Γ c).bind (castTo · .bool)
    let ⟨s, x⟩ ← infer Γ x
    return ⟨s, .ite c x (← (infer Γ y).bind (castTo · s))⟩
  | Γ, .eq a b => do
    return ⟨.bool, .eq (← (infer Γ a).bind (castTo · .int)) (← (infer Γ b).bind (castTo · .int))⟩
  | Γ, .add a b => do
    return ⟨.int, .add (← (infer Γ a).bind (castTo · .int)) (← (infer Γ b).bind (castTo · .int))⟩
  | Γ, .lam x a b => do let ⟨s, b⟩ ← infer ((x, a) :: Γ) b; return ⟨.arr a s, .lam x a b⟩
  | Γ, .app f a => do
    let ⟨.arr sa sb, f⟩ ← infer Γ f | none
    return ⟨sb, .app f (← (infer Γ a).bind (castTo · sa))⟩
  | Γ, .let_ x v b => do
    let ⟨sa, v⟩ ← infer Γ v
    let ⟨sb, b⟩ ← infer ((x, sa) :: Γ) b
    return ⟨sb, .let_ x v b⟩

/-! ## Verified optimizer -/

namespace Exp

def mkNot : Exp Γ .bool → Exp Γ .bool
  | .boolLit b => .boolLit (!b) | .not b => b | b => .not b
def mkIte : Exp Γ .bool → Exp Γ s → Exp Γ s → Exp Γ s
  | .boolLit b, x, y => if b then x else y | .not c, x, y => .ite c y x | c, x, y => .ite c x y
def mkEq : Exp Γ .int → Exp Γ .int → Exp Γ .bool
  | .intLit a, .intLit b => .boolLit (a == b) | a, b => .eq a b
def mkAdd : Exp Γ .int → Exp Γ .int → Exp Γ .int
  | .intLit 0, b => b | a, .intLit 0 => a | .intLit a, .intLit b => .intLit (a + b)
  | a, b => .add a b
/-- `(@ (lambda ((x σ)) b) v)` becomes `(let ((x v)) b)`: same name, same scope, no renaming. -/
def mkApp : Exp Γ (.arr a b) → Exp Γ a → Exp Γ b
  | .lam x _ body, v => .let_ x v body | f, v => .app f v

def opt : Exp Γ s → Exp Γ s
  | .not b => mkNot b.opt
  | .ite c x y => mkIte c.opt x.opt y.opt
  | .eq a b => mkEq a.opt b.opt
  | .add a b => mkAdd a.opt b.opt
  | .lam x a b => .lam x a b.opt
  | .app f a => mkApp f.opt a.opt
  | .let_ x v b => .let_ x v.opt b.opt
  | e => e

variable {Γ : Ctx} {s a b : SmtSort} (ρ : Env Γ)
@[simp] theorem eval_mkNot (x : Exp Γ .bool) : (mkNot x).eval ρ = !x.eval ρ := by
  unfold mkNot; split <;> simp [eval]
@[simp] theorem eval_mkIte (c : Exp Γ .bool) (x y : Exp Γ s) :
    (mkIte c x y).eval ρ = if c.eval ρ then x.eval ρ else y.eval ρ := by
  unfold mkIte; split <;> (try split) <;> simp_all [eval]
@[simp] theorem eval_mkEq (x y : Exp Γ .int) : (mkEq x y).eval ρ = (x.eval ρ == y.eval ρ) := by
  unfold mkEq; split <;> simp [eval]
@[simp] theorem eval_mkAdd (x y : Exp Γ .int) : (mkAdd x y).eval ρ = x.eval ρ + y.eval ρ := by
  unfold mkAdd; split <;> simp [eval]
@[simp] theorem eval_mkApp (f : Exp Γ (.arr a b)) (v : Exp Γ a) :
    (mkApp f v).eval ρ = f.eval ρ (v.eval ρ) := by
  unfold mkApp; split <;> simp [eval]

/-- Soundness of the optimizer. -/
theorem eval_opt (e : Exp Γ s) (ρ : Env Γ) : e.opt.eval ρ = e.eval ρ := by
  induction e <;> first | rfl | (simp_all [opt, eval]; done) | (funext; simp_all [opt, eval])

end Exp

/-- Evaluation of a typechecked term in `Γ`, optionally after optimization. -/
def NExpr.denote? (e : NExpr) (Γ : Ctx) (s : SmtSort) (ρ : Env Γ) (opt := false) :
    Option s.denote :=
  ((infer Γ e).bind (castTo · s)).map fun E => (if opt then E.opt else E).eval ρ

/-- Reflection principle: both sides typecheck, denote `lhs`/`rhs`, and agree once optimized. -/
theorem reflect_eq {Γ : Ctx} {s : SmtSort} {ρ : Env Γ} {e₁ e₂ : NExpr} {lhs rhs : s.denote}
    (h₁ : e₁.denote? Γ s ρ = some lhs) (h₂ : e₂.denote? Γ s ρ = some rhs)
    (h : e₁.denote? Γ s ρ true = e₂.denote? Γ s ρ true) : lhs = rhs := by
  have hopt (e : NExpr) : e.denote? Γ s ρ true = e.denote? Γ s ρ := by
    simp [NExpr.denote?, Exp.eval_opt]
  rw [hopt, hopt, h₁, h₂] at h
  exact Option.some.inj h

/-! ## Reification -/

partial def reifySort (e : Expr) : MetaM SmtSort := do
  match ← instantiateMVars e with
  | `(expr| Bool) => return .bool
  | `(expr| Int) => return .int
  | `(expr| (?a : Type) → (?b : Type)) => return .arr (← reifySort a) (← reifySort b)
  | e => throwError "named_reflect: unsupported sort{indentExpr e}"

/-- Object names of Lean locals, names in scope (innermost first), combinators to unfold. -/
structure NameCtx where
  names : FVarIdMap String := {}
  usedNames : List String := []
  unfold : NameSet := {}

/-- Reification monad; the state holds the free context `Γ₀` as `(name, sort, value)`. -/
abbrev ReifyM := ReaderT NameCtx (StateRefT (Array (String × SmtSort × Expr)) MetaM)

/-- `base`, or the first `base_i` not in `used`. -/
def freshName (base : String) (used : List String) : String := Id.run do
  let mut (x, i) := (base, 1)
  while used.contains x do (x, i) := (s!"{base}_{i}", i + 1)
  return x

/-- Extends the context with object name `x` for the Lean local `fv`. -/
def NameCtx.push (ctx : NameCtx) (fv : FVarId) (x : String) : NameCtx :=
  { ctx with names := ctx.names.insert fv x, usedNames := x :: ctx.usedNames }

/-- Keeps the user name `n` unless `body` mentions a live local named `n` (capture). -/
def chooseName (n : Name) (body : Expr) : ReifyM String := do
  let ctx ← read
  let base := n.eraseMacroScopes.toString (escape := false)
  let captures := body.hasAnyFVar fun v => ctx.names.get? v == some base
  return if captures then freshName base ctx.usedNames else base

partial def reify (e : Expr) : ReifyM NExpr := do
  let e ← instantiateMVars e
  if let .fvar x := e then if let some n := (← read).names.get? x then return .var n
  if let some i := e.int? then return .intLit i
  match e with
  | `(expr| true) => return .boolLit true
  | `(expr| false) => return .boolLit false
  | `(expr| !(?b : Bool)) => return .not (← reify b)
  | `(expr| @ite (_ : Type) ((?c : Bool) = true) _ ?x ?y) =>
    return .ite (← reify c) (← reify x) (← reify y)
  | `(expr| (?a : Int) == ?b) => return .eq (← reify a) (← reify b)
  | `(expr| (?a : Int) + ?b) => return .add (← reify a) (← reify b)
  -- Binders use `Expr` constructor patterns: a higher-order capture `?P x` is η-reduced,
  -- which would collapse nested binders and lose their user names.
  | .lam n α body _ =>
    let s ← reifySort α
    withLocalDeclD n α fun x => do
      let x' ← chooseName n (body.instantiate1 x)
      return .lam x' s (← withReader (·.push x.fvarId! x') (reify (body.instantiate1 x)))
  | .letE n α v body _ =>
    let v ← reify v
    withLocalDeclD n α fun x => do
      let x' ← chooseName n (body.instantiate1 x)
      return .let_ x' v (← withReader (·.push x.fvarId! x') (reify (body.instantiate1 x)))
  | _ =>
    if let .const c _ := e.getAppFn then if (← read).unfold.contains c then
      if let some e' ← unfoldDefinition? e then return ← reify e'.headBeta
    if let .app f a := e then
      let fTy ← inferType f
      if let some (.arr ..) ← (observing? (reifySort fTy) : MetaM _) then
        return .app (← reify f) (← reify a)
    throwError "named_reflect: cannot reify{indentExpr e}"

/-- Runs `k` with the free context hypotheses of SMT sorts as `declare-fun` symbols `Γ₀`. -/
def withFreeContext (unfold : NameSet) (k : ReifyM α) : MetaM (α × Ctx × Expr) := do
  let mut ctx : NameCtx := { unfold }
  let mut Γ₀ := #[]
  for (h, ty) in ← localHypTypes do
    let some s ← observing? (reifySort ty) | continue
    let x := freshName ((← h.fvarId!.getUserName).eraseMacroScopes.toString) ctx.usedNames
    ctx := ctx.push h.fvarId! x
    Γ₀ := Γ₀.push (x, s, h)
  let a ← (k.run ctx).run' Γ₀
  let (ρ, Γ) ← Γ₀.foldlM (init := (← `(expr| Env.nil), ([] : Ctx))) fun (ρ, Γ) (x, s, v) =>
    return (← `(expr| Env.cons (x := $(toExpr x)) (s := $(toExpr s)) (Γ := $(toExpr Γ)) $v $ρ),
      (x, s) :: Γ)
  return (a, Γ, ρ)

/-- `named_reflect [c₁, …]` proves `lhs = rhs` by reflection, unfolding the combinators `cᵢ`. -/
syntax (name := namedReflect) "named_reflect" (" [" ident,* "]")? : tactic

@[tactic namedReflect] def evalNamedReflect : Tactic := fun stx => withMainContext do
  let ids := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let unfold ← ids.foldlM (init := {}) fun s id =>
    return s.insert (← realizeGlobalConstNoOverloadWithInfo id)
  let `(expr| @Eq (?α : Type) ?lhs ?rhs) ← getMainTarget
    | throwError "named_reflect: expected an equation"
  let ((e₁, e₂), Γ, ρ) ← withFreeContext unfold do return (← reify lhs, ← reify rhs)
  let pf ← `(expr| @reflect_eq $(toExpr Γ) $(toExpr (← reifySort α)) $ρ $(toExpr e₁)
    $(toExpr e₂) $lhs $rhs)
  let [h₁, h₂, h] ← (← getMainGoal).apply pf | throwError "named_reflect: unexpected goals"
  for g in [h₁, h₂, h] do
    try g.refl catch _ =>
      throwError "named_reflect: failed{indentD e₁.toSmtLib}\nvs.{indentD e₂.toSmtLib}"
  replaceMainGoal []

/-- Prints the `declare-fun` context and the SMT-LIB rendering of the reified term. -/
elab "#reify_named " t:term : command => Command.runTermElabM fun _ => do
  let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
  let (ne, Γ, _) ← withFreeContext {} (reify e)
  let decls := Γ.reverse.map fun (x, s) => s!"(declare-fun {x} () {s.toSmtLib}) "
  logInfo s!"{String.join decls}{ne.toSmtLib}"

/-! ## Naming tests -/

-- Nested binders with identical user names: the inner one shadows the outer one.
/-- info: (lambda ((x Int)) (lambda ((x Int)) (+ x 1))) -/
#guard_msgs in set_option linter.unusedVariables false in
#reify_named fun (x : Int) => fun (x : Int) => x + 1

-- `addTo% e` is `fun x => e + x` with a hygienic `x`: macro scopes are erased from the name,
-- and the binder is renamed when `e` mentions an outer `x` it would otherwise capture.
macro "addTo% " e:term : term => `(fun (x : Int) => $e + x)
/-- info: (lambda ((y Int)) (lambda ((x Int)) (+ y x))) -/
#guard_msgs in #reify_named fun (y : Int) => addTo% y
/-- info: (lambda ((x Int)) (lambda ((x_1 Int)) (+ x x_1))) -/
#guard_msgs in #reify_named fun (x : Int) => addTo% x

-- Free context variables: shadowed when unused, otherwise the binder is renamed.
/-- info: (declare-fun x () Int) (@ (lambda ((x Int)) (+ x 1)) x) -/
#guard_msgs in variable (x : Int) in #reify_named (fun (x : Int) => x + 1) x
/-- info: (declare-fun x () Int) (let ((x (+ x 1))) (lambda ((x_1 Int)) (+ x x_1))) -/
#guard_msgs in variable (x : Int) in #reify_named let x := x + 1; addTo% x

/-- info: (declare-fun f () (-> Int Int)) (lambda ((b Bool)) (@ f (ite (not b) 0 -1))) -/
#guard_msgs in variable (f : Int → Int) in #reify_named fun (b : Bool) => f (if !b then 0 else -1)

/--
error: named_reflect: cannot reify
  [x].length
-/
#guard_msgs in #reify_named fun (x : Int) => [x].length

/-! ## Proofs by reflection -/

example (x : Int) : (fun x => 0 + x + 1) x = x + 1 := by named_reflect

example : (fun (x : Int) => addTo% (x + 0)) = fun x y => x + y := by named_reflect

example (x : Int) : (let x := x + 0; let y := (fun x => x) x; y) = x := by named_reflect

example (p : Bool) (x : Int) : (if !p then 1 else x) = if p then x + 0 else 1 := by named_reflect

def S {α β γ : Type} (f : α → β → γ) (g : α → β) (x : α) : γ := f x (g x)
def K {α β : Type} (a : α) (_ : β) : α := a
def I {α : Type} (a : α) : α := a
example (x : Int) : S (K (β := Int → Int)) (K (β := Int)) (0 + x) = I x := by
  named_reflect [S, K, I]

def twice (f : Int → Int) (x : Int) : Int := f (f x)
def compose (f g : Int → Int) : Int → Int := fun x => f (g x)
example (f g : Int → Int) (x : Int) : compose f g (x + 0) = twice I (f (g x)) := by
  named_reflect [compose, twice, I]

example (k : Int) :
    (fun (g : Int → Int → Int) n => g n (n + 0))
        (fun a b => if (1 + 1 : Int) == 2 then a + b else k) =
      fun n => n + n := by
  named_reflect

/--
error: named_reflect: failed
  (+ x 1)
vs.
  x
-/
#guard_msgs in example (x : Int) : x + 1 = x := by named_reflect

end ExprQuotReifyNamed
