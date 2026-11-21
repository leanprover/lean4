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
      Simp.SimpM.run' (Simp.simp target) { pre := fun e => Arith.normalizeAdd? e Simp.simp }
    match r with
    | .rfl .. => throwError "no additive expression changed"
    | .step target proof .. => replaceMainGoal [← g.replaceTargetEq target proof]

elab "module_eq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run do Arith.proveAddEq? (← shareCommon target)
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

-- Concrete numerals share the atom 1, independently of where constants occur.
example (n : Int) : n + 1 = 2 + (n - 1) := by module_eq
example (n : Int) : 1 + n = 2 + (n - 1) := by module_eq
example (n : Int) : n - 7 = -3 + (n - 4) := by module_eq
example (n : Nat) : n + 1 + 1 = 2 + n := by module_eq
example (n : Int) : n + 1 = 2 + (n - 1) := by module_nf; rfl
example (n : Nat) : n + 1 + 1 = 2 + n := by module_nf; rfl

-- A numeral from a nonstandard instance must remain an atom.
example (n : Int) (h : n + 2 = n + (1 + 1)) : n + 2 = n + (1 + 1) := by
  letI : OfNat Int 2 := ⟨5⟩
  have : n + (2 : Int) = n + (1 + 1) → n + (2 : Int) = n + (1 + 1) := by
    intro h
    fail_if_success module_eq
    exact h
  exact h

-- Normalization preserves canonical operator instances on concrete carriers.
run_meta do
  for type in [mkConst ``Nat, mkConst ``Int] do
    withLocalDeclD `a type fun a => withLocalDeclD `b type fun b => do
      let vars := #[a, b] |>.qsort Expr.lt
      let e ← mkAppM ``HAdd.hAdd #[vars[0]!, vars[1]!]
      let r ← SymM.run do Arith.normalizeAdd? (← shareCommon (← Sym.canon e))
      unless r matches .rfl .. do
        throwError "already-normal addition changed its operator instance"
      let reversed ← mkAppM ``HAdd.hAdd #[vars[1]!, vars[0]!]
      let r ← SymM.run do Arith.normalizeAdd? (← shareCommon reversed)
      unless (r.getResultExpr reversed) == e do
        throwError "additive normalization did not emit atoms in Expr.lt order"
      let r ← SymM.run do Arith.normalize? (← shareCommon reversed) fun _ => pure .rfl
      unless (r.getResultExpr reversed) == e do
        throwError "ring and additive normalization disagree on atom order"
      let e ← mkAppM ``HAdd.hAdd #[a, a]
      let r ← SymM.run do Arith.normalizeAdd? (← shareCommon e)
      let .step e' proof .. := r | throwError "repeated atom was not collected"
      unless (← inferType proof) == (← mkEq e e') do
        throwError "normalization proof does not expose the input and output terms"
      let target ← mkEq e e'
      let some proof ← SymM.run do Arith.proveAddEq? (← shareCommon target)
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
      let result ← SymM.run do Arith.proveAddEq? (← shareCommon (← mkEq lhs rhs))
      unless result.isNone do throwError "unexpected additive equality"
      if ← x.mvarId!.isAssigned then throwError "normalization assigned a metavariable"
      let _ ← SymM.run do Arith.normalizeAdd? (← shareCommon lhs)
      if ← x.mvarId!.isAssigned then throwError "normalization assigned a metavariable"

-- The atom callback can use the surrounding simplifier to normalize inside applications.
elab "module_eq_atoms" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some proof ← SymM.run do
      Simp.SimpM.run' (Arith.proveAddEq? (← shareCommon target) Simp.simp)
        { pre := fun e => Arith.normalizeAdd? e Simp.simp }
      | throwError "the additive normal forms differ"
    g.assign proof
    replaceMainGoal []

elab "module_nf_atoms" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target))
        { pre := fun e => Arith.normalizeAdd? e Simp.simp }
    let .step target proof .. := r | throwError "no additive expression changed"
    replaceMainGoal [← g.replaceTargetEq target proof]

example {M : Type u} [NatModule M] (f : M → M) (a b : M) :
    f (a + b) + f (b + a) = 2 • f (a + b) := by module_eq_atoms

-- Normalized zero must remain a numeral for subsequent simp rewrites.
example {R : Type u} [Ring R] (a b : R) : a * (b - b) = 0 := by
  module_nf_atoms
  simp only [Semiring.mul_zero]

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
      let .step e' proof _ cd ← SymM.run do Arith.normalizeAdd? (← shareCommon e) simpAtom
        | throwError "callback was not used"
      unless cd do throwError "lost the callback's context dependency"
      unless ← isDefEq (← inferType proof) (← mkEq e e') do
        throwError "unexpected callback certificate type"

-- Scalar coefficients can be evaluated by Lean's existing arithmetic normalizer.
elab "module_eq_coeffs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let simpAtom (e : Expr) : SymM Sym.Simp.Result := Arith.normalize? e (fun _ => pure .rfl)
    let some proof ← SymM.run do Arith.proveAddEq? (← shareCommon target) simpAtom
      | throwError "the additive normal forms differ"
    g.assign proof
    replaceMainGoal []

example {M : Type u} [NatModule M] (a : M) :
    (2 + 3 : Nat) • a + a = 6 • a := by module_eq_coeffs

example {M : Type u} [IntModule M] (a : M) :
    ((2 + 3 : Int) * (-2)) • a = -(5 • a + 5 • a) := by module_eq_coeffs

-- Operations are checked against the module's instances at instances transparency, so an
-- instance built from a semireducible alias is not the module's operation.
private def subAlias {M : Type u} [IntModule M] (a b : M) : M := a - b
section
variable {M : Type u} [IntModule M]
local instance : Sub M := ⟨subAlias⟩
example (a b : M) (h : a - b = a + -b) : a - b = a + -b := by
  fail_if_success module_eq
  exact h
end

-- Semireducible atoms are not unfolded.
private def atomAlias {M : Type u} (a : M) : M := a
example {M : Type u} [NatModule M] (a b : M) :
    atomAlias a + b = a + b := by
  fail_if_success module_eq
  rfl

-- Metadata on additive operations must not hide their structure (#15619).
run_meta do
  withLocalDeclD `a (mkConst ``Int) fun a => do
    let add ← mkAppM ``HAdd.hAdd #[a, a]
    let sub ← mkAppM ``HSub.hSub #[a, a]
    let neg ← mkAppM ``Neg.neg #[a]
    let smul ← mkAppM ``HSMul.hSMul #[toExpr (3 : Int), a]
    for e in [add, sub, neg, smul] do
      let annotated := mkMData {} e
      let some proof ← SymM.run do Arith.proveAddEq? (← shareCommon (← mkEq annotated e))
        | throwError "metadata prevented additive equality normalization"
      checkWithKernel proof
      for input in [annotated, ← mkAppM ``HAdd.hAdd #[annotated, a]] do
        let .step output proof .. ← SymM.run do Arith.normalizeAdd? (← shareCommon input)
          | throwError "metadata prevented additive term normalization"
        if (output.find? (· matches .mdata ..)).isSome then
          throwError "normalization retained metadata"
        unless ← isDefEq (← inferType proof) (← mkEq input output) do
          throwError "unexpected metadata certificate type"
        checkWithKernel proof

-- Over `sym.arith.maxTerms`, a sum is an atom whose summands are normalized.
section
variable {M : Type u} [NatModule M]
set_option sym.arith.maxTerms 2 in
example (a b c : M) (h : a + b + c = c + b + a) : a + b + c = c + b + a := by
  fail_if_success module_eq
  exact h
set_option sym.arith.maxTerms 2 in
example (a b c : M) : (b + a) + c = (a + b) + c := by module_eq
end
