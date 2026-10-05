import Lean

/-!
Additive equality certificates for modules over natural numbers or integers.
Multiplication and symbolic scalar multiplication remain atoms. In particular,
the carrier need not have cancellation, a multiplicative identity, or associative multiplication.
-/

open Lean Meta Elab Tactic Sym

elab "module_nf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      let target ← shareCommon target
      Simp.SimpM.run' (Simp.simp target) { post := fun e => Arith.normalizeAdd? e }
    match r with
    | .rfl .. => throwError "no additive expression changed"
    | .step target proof .. => replaceMainGoal [← g.replaceTargetEq target proof]

elab "module_eq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run (Arith.proveAddEq? target)
      | throwError "the additive normal forms differ"
    unless ← isDefEq (← inferType proof) target do
      throwError "unexpected certificate type"
    g.assign proof
    replaceMainGoal []

open Lean.Grind

example {M : Type u} [NatModule M] (a b c : M) :
    a + (b + c) = c + a + b := by module_eq

example {M : Type u} [NatModule M] (a b : M) :
    2 • (a + b) + a = 3 • a + 2 • b := by module_eq

example {M : Type u} [NatModule M] (a : M) : 0 • a + a = a := by module_eq

example {M : Type u} [NatModule M] : (0 : M) + 0 = 0 := by module_eq

example {M : Type u} [IntModule M] (a b : M) :
    a + b + b - a = (2 : Int) • b := by module_eq

example {M : Type u} [IntModule M] (a b : M) :
    -((3 : Nat) • a) + (2 : Int) • (a - b) = -a - (2 : Int) • b := by module_eq

example {M : Type u} [IntModule M] (a : M) : a + -a = 0 := by module_eq

example {M : Type u} [NatModule M] [Mul M] (a b : M) :
    a * b + a * b + b * a = 2 • (a * b) + b * a := by module_eq

private abbrev alias {M : Type u} (a : M) := a

example {M : Type u} [NatModule M] [Mul M] (a b : M) :
    alias (a * b) + a * b = 2 • (a * b) := by module_eq

example {M : Type u} [NatModule M] (a : M) :
    letI : SMul Nat M := ⟨fun _ a => a⟩
    2 • a = a + a → 2 • a = a + a := by
  intro h
  fail_if_success module_eq
  exact h

example {M : Type u} [IntModule M] [Mul M] (a b c : M)
    (h : a * (b * c) = (a * b) * c) : a * (b * c) = (a * b) * c := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] [Mul M] (a b : M) (h : a * b = b * a) :
    a * b = b * a := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (a b : M) (n : Nat) :
    n • a + b = b + n • a := by module_eq

example (a b : Nat) (h : a - b + b = a) : a - b + b = a := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (a b : M) :
    letI : HAdd M M M := ⟨fun a _ => a⟩
    a + b = b + a → a + b = b + a := by
  intro h
  fail_if_success module_eq
  exact h

example (a b : Bool) (h : a = b) : a = b := by
  fail_if_success module_eq
  exact h

example {M : Type u} [NatModule M] (f : M → M) (a b : M) :
    f (a + b) = f (b + a) := by module_nf; rfl

example {M : Type u} [IntModule M] (P : M → Prop) (a b : M) (h : P b) :
    P (a + b - a) := by module_nf; exact h

example {M : Type u} [NatModule M] [Mul M] (a b : M) (P : M → Prop)
    (h : P (2 • (a * b))) : P (a * b + a * b) := by module_nf; exact h

example {M : Type u} [IntModule M] (a b : M) : a + b + a = a + a + b := by
  module_nf
  fail_if_success module_nf
  rfl

-- Normalization preserves canonical operator instances on concrete carriers.
run_meta do
  for type in [mkConst ``Nat, mkConst ``Int] do
    withLocalDeclD `a type fun a => withLocalDeclD `b type fun b => do
      let vars := #[a, b] |>.qsort Expr.lt
      let e ← mkAppM ``HAdd.hAdd #[vars[1]!, vars[0]!]
      let r ← SymM.run do Arith.normalizeAdd? (← shareCommon (← Sym.canon e))
      unless r matches .rfl .. do
        throwError "already-normal addition changed its operator instance"
      let e ← mkAppM ``HAdd.hAdd #[a, a]
      let r ← SymM.run (Arith.normalizeAdd? e)
      let .step e' proof .. := r | throwError "repeated atom was not collected"
      unless (← inferType proof) == (← mkEq e e') do
        throwError "normalization proof does not expose the input and output terms"
      let target ← mkEq e e'
      let some proof ← SymM.run (Arith.proveAddEq? target)
        | throwError "normalized terms were not equal"
      unless (← inferType proof) == target do
        throwError "equality proof does not expose the input proposition"

-- Failed equality normalization must not assign the caller's metavariables.
run_meta do
  let type := mkConst ``Nat
  withLocalDeclD `a type fun a => withLocalDeclD `b type fun b =>
    withLocalDeclD `c type fun c => do
      let x ← mkFreshExprMVar type
      let lhs ← mkAppM ``HAdd.hAdd #[x, a]
      let rhs ← mkAppM ``HAdd.hAdd #[c, b]
      let result ← SymM.run (Arith.proveAddEq? (← mkEq lhs rhs))
      unless result.isNone do throwError "unexpected additive equality"
      if ← x.mvarId!.isAssigned then throwError "normalization assigned a metavariable"
      let _ ← SymM.run (Arith.normalizeAdd? lhs)
      if ← x.mvarId!.isAssigned then throwError "normalization assigned a metavariable"

-- The atom callback can use the surrounding simplifier to normalize inside applications.
elab "module_eq_atoms" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run do
      Simp.SimpM.run' (Arith.proveAddEq? (← shareCommon target) Simp.simp)
        { post := fun e => Arith.normalizeAdd? e Simp.simp }
      | throwError "the additive normal forms differ"
    g.assign proof
    replaceMainGoal []

elab "module_nf_atoms" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target))
        { post := fun e => Arith.normalizeAdd? e Simp.simp }
    let .step target proof .. := r | throwError "no additive expression changed"
    replaceMainGoal [← g.replaceTargetEq target proof]

example {M : Type u} [NatModule M] (f : M → M) (a b : M) :
    f (a + b) + f (b + a) = 2 • f (a + b) := by module_eq_atoms

example {M : Type u} [IntModule M] (f : M → M) (a b : M) :
    f (a + b) - f (b + a) = 0 := by module_eq_atoms

example {M : Type u} [NatModule M] (f : M → M) (a b : M) (P : M → Prop)
    (h : ∀ x, P (2 • f x)) : P (f (a + b) + f (b + a)) := by
  module_nf_atoms
  exact h _

-- Callback proofs remain attached when the prepared expression already is a normal form.
example {M : Type u} [NatModule M] (f : M → M) (a b c : M) :
    f (a + b) + c = f (b + a) + c := by module_eq_atoms

-- Context-dependent callback proofs must remain context-dependent after normalization.
run_meta do
  let type := mkConst ``Nat
  withLocalDeclD `a type fun a => withLocalDeclD `b type fun b => do
    let eq ← mkEq a b
    withLocalDeclD `h eq fun h => do
      let simpAtom (e : Expr) : SymM Sym.Simp.Result := do
        if isSameExpr e a then return .step b h (contextDependent := true)
        return .rfl
      let e ← mkAppM ``HAdd.hAdd #[a, a]
      let .step e' proof _ cd ← SymM.run (Arith.normalizeAdd? e simpAtom)
        | throwError "callback was not used"
      unless cd do throwError "lost the callback's context dependency"
      unless ← isDefEq (← inferType proof) (← mkEq e e') do
        throwError "unexpected callback certificate type"

-- Scalar coefficients can be evaluated by Lean's existing arithmetic normalizer.
elab "module_eq_coeffs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run (Arith.proveAddEq? target fun e =>
      Arith.normalize? e (fun _ => pure .rfl))
      | throwError "the additive normal forms differ"
    g.assign proof
    replaceMainGoal []

example {M : Type u} [NatModule M] (a : M) :
    (2 + 3 : Nat) • a + a = 6 • a := by module_eq_coeffs

example {M : Type u} [IntModule M] (a : M) :
    ((2 + 3 : Int) * (-2)) • a = -(5 • a + 5 • a) := by module_eq_coeffs

-- Semireducible aliases of module operations remain valid operations.
private def subAlias {M : Type u} [IntModule M] (a b : M) : M := a - b
private def zeroAlias {M : Type u} [NatModule M] : M := 0
section
variable {M : Type u} [IntModule M]
local instance : Sub M := ⟨subAlias⟩
example (a b : M) : a - b = a + -b := by module_eq
example (a b : M) : a - b + b = a := by module_eq
end
section
variable {M : Type u} [NatModule M]
local instance : Zero M := ⟨zeroAlias⟩
example (a : M) : a + 0 = a := by module_eq
end

-- Default transparency for operations does not unfold semireducible atoms.
private def atomAlias {M : Type u} (a : M) : M := a
example {M : Type u} [NatModule M] (a b : M) :
    atomAlias a + b = a + b := by
  fail_if_success module_eq
  rfl
