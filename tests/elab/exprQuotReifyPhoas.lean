import Lean

/-!
# PHOAS reification of a higher-order SMT-LIB fragment with `expr` quotations

Lean terms over `Bool`, `Int` and functions are reified into a PHOAS rendering of SMT-LIB 2.7
(`true`, `not`, `ite`, `=`, `+`, `lambda`, `@`, `let`, and `declare-fun` symbols as `atom`s),
simplified by the verified `Term.norm`, and equations are proved by reflection (`smt_norm`).
Going under a Lean binder, the reifier introduces a Lean local `x` and a PHOAS variable
`rx : rep s`, records `x ↦ rx` in an `FVarIdMap`, and closes the body with `mkLambdaFVars`.
-/

namespace ExprQuotReifyPhoas
open Lean Meta Elab Tactic

/-- SMT-LIB sorts `Bool`, `Int` and `(-> σ τ)`. -/
inductive SmtSort where
  | bool | int | arr (dom cod : SmtSort)
  deriving ToExpr

@[reducible] def SmtSort.denote : SmtSort → Type
  | .bool => Bool | .int => Int | .arr a b => a.denote → b.denote

/-- PHOAS terms; `lam` and `let_` bind object variables with Lean functions. -/
inductive Term (rep : SmtSort → Type) : SmtSort → Type where
  | var : rep s → Term rep s
  /-- A `declare-fun` symbol: an opaque Lean value, e.g. a free context variable. -/
  | atom (s : SmtSort) : s.denote → Term rep s
  | boolLit : Bool → Term rep .bool
  | intLit : Int → Term rep .int
  | not : Term rep .bool → Term rep .bool
  | ite : Term rep .bool → Term rep s → Term rep s → Term rep s
  | eq : Term rep .int → Term rep .int → Term rep .bool
  | add : Term rep .int → Term rep .int → Term rep .int
  | lam : (rep a → Term rep b) → Term rep (.arr a b)
  | app : Term rep (.arr a b) → Term rep a → Term rep b
  | let_ : Term rep a → (rep a → Term rep b) → Term rep b

/-- Closed terms are parametric in the variable representation. -/
def ClosedTerm (s : SmtSort) : Type 1 := (rep : SmtSort → Type) → Term rep s

def Term.denote : Term SmtSort.denote s → s.denote
  | .var x | .atom _ x | .boolLit x | .intLit x => x
  | .not b => !b.denote
  | .ite c x y => if c.denote then x.denote else y.denote
  | .eq a b => a.denote == b.denote
  | .add a b => a.denote + b.denote
  | .lam f => fun x => (f x).denote
  | .app f a => f.denote a.denote
  | .let_ a f => (f a.denote).denote

/-! ## Verified simplifier -/

namespace Term
variable {rep : SmtSort → Type}

def mkNot : Term rep .bool → Term rep .bool
  | .boolLit b => .boolLit (!b) | .not b => b | b => .not b
def mkIte : Term rep .bool → Term rep s → Term rep s → Term rep s
  | .boolLit b, x, y => if b then x else y | .not c, x, y => .ite c y x | c, x, y => .ite c x y
def mkEq : Term rep .int → Term rep .int → Term rep .bool
  | .intLit a, .intLit b => .boolLit (a == b) | a, b => .eq a b
def mkAdd : Term rep .int → Term rep .int → Term rep .int
  | .intLit 0, b => b | a, .intLit 0 => a | .intLit a, .intLit b => .intLit (a + b)
  | a, b => .add a b
/-- A variable-bound `let` is inlined: copy propagation needs no substitution in PHOAS. -/
def mkLet : Term rep a → (rep a → Term rep b) → Term rep b
  | .var v, f => f v | x, f => .let_ x f
/-- A β-redex becomes a `let`. -/
def mkApp : Term rep (.arr a b) → Term rep a → Term rep b
  | .lam f, x => mkLet x f | f, x => .app f x

/-- Bottom-up single-pass simplifier, parametric in `rep`. -/
def norm : Term rep s → Term rep s
  | .not b => mkNot b.norm
  | .ite c x y => mkIte c.norm x.norm y.norm
  | .eq a b => mkEq a.norm b.norm
  | .add a b => mkAdd a.norm b.norm
  | .lam f => .lam fun x => (f x).norm
  | .app f a => mkApp f.norm a.norm
  | .let_ a f => mkLet a.norm fun x => (f x).norm
  | e => e

variable {s a b : SmtSort}
@[simp] theorem denote_mkNot (x : Term _ .bool) : (mkNot x).denote = !x.denote := by
  unfold mkNot; split <;> simp [denote]
@[simp] theorem denote_mkIte (c : Term _ .bool) (x y : Term _ s) :
    (mkIte c x y).denote = if c.denote then x.denote else y.denote := by
  unfold mkIte; split <;> (try split) <;> simp_all [denote]
@[simp] theorem denote_mkEq (x y : Term _ .int) : (mkEq x y).denote = (x.denote == y.denote) := by
  unfold mkEq; split <;> simp [denote]
@[simp] theorem denote_mkAdd (x y : Term _ .int) : (mkAdd x y).denote = x.denote + y.denote := by
  unfold mkAdd; split <;> simp [denote]
@[simp] theorem denote_mkLet (x : Term _ a) (f : a.denote → Term _ b) :
    (mkLet x f).denote = (f x.denote).denote := by
  unfold mkLet; split <;> simp [denote]
@[simp] theorem denote_mkApp (f : Term _ (.arr a b)) (x : Term _ a) :
    (mkApp f x).denote = f.denote x.denote := by
  unfold mkApp; split <;> simp [denote]

/-- Soundness of the simplifier. -/
theorem denote_norm (e : Term SmtSort.denote s) : e.norm.denote = e.denote := by
  induction e <;> first | rfl | (simp_all [norm, denote]; done) | (funext; simp_all [norm, denote])

end Term

/-- Reflection principle used by `smt_norm`. -/
theorem eq_of_norm (T₁ T₂ : ClosedTerm s)
    (h : (T₁ _).norm.denote = (T₂ _).norm.denote) : (T₁ _).denote = (T₂ _).denote := by
  simpa only [Term.denote_norm] using h

/-! ## Reification -/

partial def reifySort (e : Expr) : MetaM SmtSort := do
  match ← instantiateMVars e with
  | `(expr| Bool) => return .bool
  | `(expr| Int) => return .int
  | `(expr| (?a : Type) → (?b : Type)) => return .arr (← reifySort a) (← reifySort b)
  | e => throwError "smt_norm: unsupported sort{indentExpr e}"

/-- Reifier context: the `rep` binder, object-binder map, and combinators to unfold. -/
structure Ctx where
  rep : Expr
  vars : FVarIdMap Expr := {}
  unfold : NameSet := {}

/-- Reifies `e` to `(s, t)` with `t : Term rep s`. -/
partial def reify (ctx : Ctx) (e : Expr) : MetaM (SmtSort × Expr) := do
  let rep := ctx.rep
  let e ← instantiateMVars e
  if let .fvar x := e then if let some rx := ctx.vars.get? x then
    let s ← reifySort (← inferType e)
    return (s, ← `(expr| @Term.var $rep $(toExpr s) $rx))
  if let some i := e.int? then return (.int, ← `(expr| @Term.intLit $rep $(toExpr i)))
  match e with
  | `(expr| true) => return (.bool, ← `(expr| @Term.boolLit $rep true))
  | `(expr| false) => return (.bool, ← `(expr| @Term.boolLit $rep false))
  | `(expr| !(?b : Bool)) => return (.bool, ← `(expr| @Term.not $rep $((← reify ctx b).2)))
  | `(expr| @ite (_ : Type) ((?c : Bool) = true) _ ?x ?y) =>
    let (s, x) ← reify ctx x
    let c := (← reify ctx c).2; let y := (← reify ctx y).2
    return (s, ← `(expr| @Term.ite $rep $(toExpr s) $c $x $y))
  | `(expr| (?a : Int) == ?b) =>
    return (.bool, ← `(expr| @Term.eq $rep $((← reify ctx a).2) $((← reify ctx b).2)))
  | `(expr| (?a : Int) + ?b) =>
    return (.int, ← `(expr| @Term.add $rep $((← reify ctx a).2) $((← reify ctx b).2)))
  | `(expr| fun (x : (?α : Type)) => ?P x) =>
    let n := match e.consumeMData with | .lam n .. => n | _ => `x
    let (a, b, f) ← reifyBinder ctx n α fun x => P.beta #[x]
    return (.arr a b, ← `(expr| @Term.lam $rep $(toExpr a) $(toExpr b) $f))
  | `(expr| let y : (?α : Type) := ?v; ?P y) =>
    let v := (← reify ctx v).2
    let n := match e.consumeMData with | .letE n .. => n | _ => `y
    let (a, b, f) ← reifyBinder ctx n α fun y => P.beta #[y]
    return (b, ← `(expr| @Term.let_ $rep $(toExpr a) $(toExpr b) $v $f))
  | _ =>
    if let .const c _ := e.getAppFn then if ctx.unfold.contains c then
      if let some e' ← unfoldDefinition? e then return ← reify ctx e'.headBeta
    if let .app f a := e then
      if let some (.arr sa sb) ← observing? (reifySort (← inferType f)) then
        let f := (← reify ctx f).2; let a := (← reify ctx a).2
        return (sb, ← `(expr| @Term.app $rep $(toExpr sa) $(toExpr sb) $f $a))
    if e.hasAnyFVar ctx.vars.contains then
      throwError "smt_norm: cannot reify subterm mentioning a bound variable{indentExpr e}"
    let s ← reifySort (← inferType e)
    return (s, ← `(expr| @Term.atom $rep $(toExpr s) $e))
where
  /-- Reifies `mkBody x` under a Lean binder `n : α` into a PHOAS function `fun rx => t`. -/
  reifyBinder (ctx : Ctx) (n : Name) (α : Expr) (mkBody : Expr → Expr) :
      MetaM (SmtSort × SmtSort × Expr) := do
    let a ← reifySort α
    withLocalDeclD n α fun x => withLocalDeclD n (mkApp ctx.rep (toExpr a)) fun rx => do
      let (b, t) ← reify { ctx with vars := ctx.vars.insert x.fvarId! rx } (mkBody x)
      return (a, b, ← mkLambdaFVars #[rx] t)

/-- Reifies `e` to a closed term `fun rep => …`. -/
def reifyClosed (e : Expr) (unfold : NameSet := {}) : MetaM (SmtSort × Expr) := do
  withLocalDeclD `rep (← `(expr| SmtSort → Type)) fun rep => do
    let (s, t) ← reify { rep, unfold } e
    return (s, ← mkLambdaFVars #[rep] t)

/-- `smt_norm [c₁, …]` proves `lhs = rhs` by reflection, unfolding the combinators `cᵢ`. -/
syntax (name := smtNorm) "smt_norm" (" [" ident,* "]")? : tactic

@[tactic smtNorm] def evalSmtNorm : Tactic := fun stx => withMainContext do
  let ids := if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let unfold ← ids.foldlM (init := {}) fun s id =>
    return s.insert (← realizeGlobalConstNoOverloadWithInfo id)
  let `(expr| @Eq (?α : Type) ?lhs ?rhs) ← getMainTarget
    | throwError "smt_norm: expected an equation"
  let s ← reifySort α
  let pf ← `(expr| @eq_of_norm $(toExpr s) $((← reifyClosed lhs unfold).2)
    $((← reifyClosed rhs unfold).2))
  let [h] ← (← getMainGoal).apply pf | throwError "smt_norm: unexpected subgoals"
  try h.refl catch _ => throwError "smt_norm: normal forms differ{indentExpr (← h.getType)}"
  replaceMainGoal []

/-- Prints the closed term reified from a term. -/
elab "#reify " t:term : command => Command.liftTermElabM do
  let (_, T) ← reifyClosed (← instantiateMVars (← Term.elabTermAndSynthesize t none))
  withOptions (pp.fieldNotation.set · false) do logInfo ((← ppExpr T).pretty 100)

/-! ## Reification tests -/

/-- info: fun rep => Term.lam fun x => Term.lam fun y => Term.add (Term.var x) (Term.var y) -/
#guard_msgs in #reify fun (x y : Int) => x + y

-- Shadowed binder names become distinct PHOAS variables.
/--
info: fun rep =>
  Term.lam fun x =>
    Term.let_ (Term.add (Term.var x) (Term.intLit 1)) fun x => Term.eq (Term.var x) (Term.intLit 2)
-/
#guard_msgs in #reify fun (x : Int) => let x := x + 1; x == 2

-- A `declare-fun` symbol is an atom; its application is the higher-order `app`.
opaque g : Int → Int
/--
info: fun rep =>
  Term.lam fun b =>
    Term.app (Term.atom (SmtSort.arr SmtSort.int SmtSort.int) g)
      (Term.ite (Term.not (Term.var b)) (Term.intLit 0) (Term.intLit (-1)))
-/
#guard_msgs in #reify fun (b : Bool) => g (if !b then 0 else -1)

/--
error: smt_norm: cannot reify subterm mentioning a bound variable
  [x✝].length
-/
#guard_msgs in #reify fun (x : Int) => [x].length

/-! ## Proofs by reflection (free context variables play `declare-const`/`declare-fun`) -/

example (x : Int) : 0 + x + 0 = x := by smt_norm

example (p : Bool) (x y : Int) : (if !!p then x else y) = if p then x + 0 else y := by smt_norm

example (x : Int) : (fun f : Int → Int => f (f x)) (fun y => y + 0) = x := by smt_norm

example : (fun x : Int => (fun x : Int => x + 0) (0 + x)) = fun x => x := by smt_norm

example (x : Int) : (let y := x + 0; if y == y + 0 then y else 0) = if x == x then x else 0 := by
  smt_norm

example (f : Int → Int → Int) (a : Int) : (fun h => h a (0 + a)) f = f a a := by smt_norm

example (c : Int) : (fun (k : Int → Int) (n : Int) => k (n + 0)) (· + c) = (· + c) := by
  smt_norm

def twice (f : Int → Int) (x : Int) : Int := f (f x)
example (x : Int) : twice (fun y => if 2 + 2 == 4 then y + 0 else 7) x = x := by
  smt_norm [twice]

def compose {α β γ : Type} (f : β → γ) (g : α → β) (x : α) : γ := f (g x)
example (f g : Int → Int) (x : Int) : compose f g (x + 0) = f (g x) := by smt_norm [compose]

/--
error: smt_norm: normal forms differ
  (Term.atom SmtSort.bool b).not.norm.denote = (Term.atom SmtSort.bool b).norm.denote
-/
#guard_msgs in example (b : Bool) : (!b) = b := by smt_norm

end ExprQuotReifyPhoas
