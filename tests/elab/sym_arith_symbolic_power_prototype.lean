module
public import Lean
public meta import Lean.Meta.Sym.Arith.Norm
public meta import Lean.Meta.Sym.Simp.Arith
public meta import Lean.Meta.Sym.Simp.EvalGround
public meta import Lean.Meta.Check

/-!
Symbolic-power normalization prototype for #15480. Arithmetic in bases and natural-number
exponents uses the existing `Sym.Arith` polynomial computation and certificates. Power
identities reduce nested powers, product powers, and sums or numeral coefficients in exponents.
The test tactic supplies ordinary `Sym.simp` traversal and checks the completed proof.
-/

namespace SymbolicExponentPrototype
open Lean.Grind

public theorem pow_pow {R : Type u} [Semiring R] (a : R) (m n : Nat) :
    (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih => rw [Semiring.pow_succ, ih, Nat.mul_succ, Semiring.pow_add]

public theorem pow_coeff {R : Type u} [Semiring R] (a : R) (c n : Nat) :
    a ^ (c * n) = (a ^ n) ^ c := by
  rw [pow_pow, Nat.mul_comm]

end SymbolicExponentPrototype

public meta section
open Lean Meta Elab Tactic
open Lean.Meta.Sym

namespace SymbolicExponentPrototype

private def chain (e : Expr) (r s : Sym.Simp.Result) : SymM Sym.Simp.Result := do
  match r with
  | .rfl .. => pure s
  | .step e' h _ cd => Sym.Simp.mkEqTransResult e e' h s cd

private def congrBin (e : Expr) (ra rb : Sym.Simp.Result) : SymM Sym.Simp.Result := do
  match h : e with
  | .app fa@h':(.app f a) b =>
    let rf ← Sym.Simp.mkCongrArg fa f a ra h'
    Sym.Simp.mkCongr e fa b rf rb (h' ▸ h)
  | _ => unreachable!

private def rewrite (name : Name) (args : Array Expr) : SymM Sym.Simp.Result := do
  let proof ← mkAppM name args
  let type ← Meta.inferType proof
  let_expr Eq _ _ rhs := type | throwError "expected an equality lemma"
  return .step (← shareCommon (← canon rhs)) proof

private def pow? (e : Expr) : Option (Expr × Expr) := do
  let_expr HPow.hPow _ _ _ _ a b := e | none
  return (a, b)

private def mul? (e : Expr) : Option (Expr × Expr) := do
  let_expr HMul.hMul _ _ _ _ a b := e | none
  return (a, b)

private def add? (e : Expr) : Option (Expr × Expr) := do
  let_expr HAdd.hAdd _ _ _ _ a b := e | none
  return (a, b)

private def functions? (α : Expr) : SymM (Option (Expr × Expr)) := do
  let kind ← match (← Arith.classify? α) with
    | .commRing id => pure (Arith.Kind.commRing id)
    | .commSemiring id => pure (Arith.Kind.commSemiring id)
    | _ => return none
  let action : Arith.NormM (Expr × Expr) := do
    if kind.isRing then return (← Arith.getPowFn, ← Arith.getMulFn)
    else return (← Arith.getPowFn', ← Arith.getMulFn')
  return some (← (action.run { kind }).run' {})

/-- Rewrite symbolic powers, using Lean's polynomial normalizer for bases and exponents. -/
partial def normalize (e : Expr) : SymM Sym.Simp.Result := do
  let_expr HPow.hPow α β _ _ base exponent := e |
    return ← Arith.normalize? e normalize
  unless β.isConstOf ``Nat do return .rfl
  let some (powFn, mulFn) ← functions? α | return .rfl
  unless isSameExpr powFn (← shareCommon (← canon e.appFn!.appFn!)) do return .rfl
  let r ← congrBin e (← normalize base) (← normalize exponent)
  let e' := r.getResultExpr e
  let base := e'.appFn!.appArg!
  let exponent := e'.appArg!
  let finish (s : Sym.Simp.Result) : SymM Sym.Simp.Result := do
    chain e r (← chain e' s (← normalize (s.getResultExpr e')))
  if let some (a, m) := pow? base then
    if isSameExpr powFn (← shareCommon (← canon base.appFn!.appFn!)) then
      return ← finish (← rewrite ``pow_pow #[a, m, exponent])
  if let some (a, b) := mul? base then
    if isSameExpr mulFn (← shareCommon (← canon base.appFn!.appFn!)) then
      return ← finish (← rewrite ``Lean.Grind.CommSemiring.mul_pow #[a, b, exponent])
  if let some (a, b) := add? exponent then
    if (← withReducibleAndInstances <| isDefEq exponent (mkApp2 (mkConst ``Nat.add) a b)) then
      return ← finish (← rewrite ``Lean.Grind.Semiring.pow_add #[base, a, b])
  if let some (a, b) := mul? exponent then
    unless (← withReducibleAndInstances <| isDefEq exponent (mkApp2 (mkConst ``Nat.mul) a b)) do
      return r
    let coeff? := match (Sym.getNatValue? a).run, (Sym.getNatValue? b).run with
      | some c, _ => some (a, b, c, false)
      | _, some c => some (b, a, c, true)
      | _, _ => none
    if let some (c, n, value, swap) := coeff? then
      if value > 1 then
        let s ← if swap then rewrite ``pow_pow #[base, n, c] >>= fun s => do
            match s with
            | .step _ proof .. =>
              return .step (← shareCommon (← canon (← Meta.inferType proof).appFn!.appArg!)) (← mkEqSymm proof)
            | _ => unreachable!
          else rewrite ``pow_coeff #[base, c, n]
        -- The new outer exponent is a numeral: let the existing polynomial certificate expand it.
        return ← chain e r (← chain e' s (← Arith.normalize? (s.getResultExpr e') normalize))
  let baseValue : Option Nat := (Sym.getNatValue? base).run
  if baseValue == some 1 then
    return ← chain e r (← (do
      let proof ← mkAppOptM ``Lean.Grind.Semiring.one_pow #[some α, none, some exponent]
      let type ← Meta.inferType proof
      return Sym.Simp.Result.step (← shareCommon type.appArg!) proof))
  return ← chain e r (← Arith.normalize? e' normalize)

elab "power_nf" : tactic => do
  let goal ← getMainGoal
  let proof ← goal.withContext <| SymM.run do
    let target ← shareCommon (← canon (← goal.getType))
    let initial ← Sym.simp target { pre := Sym.Simp.simpArith, post := Sym.Simp.evalGround }
    let r ← chain target initial (← normalize (initial.getResultExpr target))
    let e ← shareCommon (← canon (r.getResultExpr target))
    let r ← chain target r (← Arith.normalize? e (fun _ => pure .rfl))
    let e := r.getResultExpr target
    let proof ← if e.isTrue then pure (mkConst ``True.intro) else do
      let_expr Eq _ lhs rhs := e | throwError "expected an equality"
      unless (← isDefEq lhs rhs) do throwError "unequal normal forms:{indentExpr e}"
      Sym.mkEqRefl lhs
    match r with
    | .rfl .. => pure proof
    | .step _ h .. => mkEqMPR h proof
  goal.withContext <| checkWithKernel proof
  goal.assign proof
  replaceMainGoal []

end SymbolicExponentPrototype

end

open Lean.Grind

example (x : Int) (n : Nat) : x^(n+n) = (x^n)^2 := by
  power_nf

example (x : Int) (m n : Nat) : x^(2*m+3*n+1) = (x^m)^2*(x^n)^3*x := by
  power_nf

example (x : Int) (m n : Nat) : x^(m*n) = x^(n*m) := by
  power_nf

example (x : Int) (m n : Nat) : x^((m+n)^3) = x^(m^3+3*m^2*n+3*m*n^2+n^3) := by
  power_nf

example {R : Type} [CommSemiring R] (x : R) (m n : Nat) : (x^m)^n = x^(m*n) := by
  power_nf

example (x : Int) (m n k : Nat) : ((x^m)^n)^k = x^(m*n*k) := by
  power_nf

example (x : Rat) (m n : Nat) : (x^(m+1))^n = x^(n*(m+1)) := by
  power_nf

example (x : Int) (m n : Nat) : (x^(m+1))^(n+2) = x^(m*n+2*m+n+2) := by
  power_nf

example (x y : Int) (m n : Nat) : ((x+y)^m)^n = (x+y)^(m*n) := by
  power_nf

example (x : Int) (n : Nat) : (x^2)^n = x^(2*n) := by
  power_nf

example (x : Int) (n : Nat) : (x^n)^3 = x^(3*n) := by
  power_nf

example (x : Int) (m n k : Nat) : (x^(m+n))^k = x^(m*k)*x^(n*k) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (n : Nat) : (x*y)^n = x^n*y^n := by
  power_nf

example (x y z : Nat) (n : Nat) : (x*y*z)^n = x^n*y^n*z^n := by
  power_nf

example (x : Int) (n : Nat) : ((2 : Int)*x)^n = (2 : Int)^n*x^n := by
  power_nf

example (x y : Int) (m n k : Nat) : (x^m*y^k)^n = x^(m*n)*y^(k*n) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (n : Nat) : (x*y)^(n+2) = x^n*y^n*x^2*y^2 := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (m n : Nat) : ((x*y)^m)^n = x^(m*n)*y^(m*n) := by
  power_nf

example (x y : Int) (n : Nat) : ((x+y)^2)^n = (x^2+2*x*y+y^2)^n := by
  power_nf

example (x y : Int) (m n : Nat) : (x*y+y*x)^(m+n) = (2*x*y)^m*(2*x*y)^n := by
  power_nf

example (x y : Int) (m n : Nat) : (x^n+y^m)^2 = x^(2*n)+2*x^n*y^m+y^(2*m) := by
  power_nf

example (x y : Rat) (m n : Nat) : (x^n+y^m)^3 = x^(3*n)+3*x^(2*n)*y^m+3*x^n*y^(2*m)+y^(3*m) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (m n : Nat) : (2*x^n+3*y^m)^2 = 4*x^(2*n)+12*x^n*y^m+9*y^(2*m) := by
  power_nf

example (x y : Int) (m n : Nat) : (x^n+y^m)*(x^n-y^m) = x^(2*n)-y^(2*m) := by
  power_nf

example (m n : Nat) : (0 : Int)^((m+1)*(n+1)) = 0 := by
  power_nf

example (m n : Nat) : ((2 : Int)^m)^n = (2 : Int)^(m*n) := by
  power_nf

example (x : Rat) (n : Nat) : (x/2)^n = x^n*(1/2 : Rat)^n := by
  power_nf

example (x y : Rat) (m n : Nat) : (x^n/2+y^m/3)^2 = x^(2*n)/4+x^n*y^m/3+y^(2*m)/9 := by
  power_nf

example (x : Rat) (m n : Nat) : (x^(m+1))^n = x^(n*(m+1)) := by
  power_nf

example (x : Int) (n : Nat) : x^(2^(n+1)) = (x^(2^n))^2 := by
  power_nf

example {R : Type} [CommSemiring R] (x : R) (n : Nat) : x = x*1^n := by
  power_nf


example : True := by
  fail_if_success have : ∀ (n : Nat), (0 : Int)^n = 0 := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (n : Nat), (0 : Rat)^n = 0 := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Int) (m n : Nat), x^(m+n) = x^m+x^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Rat) (m n : Nat), x^(m+n) = x^m+x^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x y : Int) (n : Nat), (x+y)^n = x^n+y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x y : Rat) (n : Nat), (x+y)^n = x^n+y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Int) (m n : Nat), (x^m)^n = x^(m+n) := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Rat) (m n : Nat), (x^m)^n = x^(m+n) := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ {R : Type} [Lean.Grind.Semiring R] (x y : R) (n : Nat), (x*y)^n = x^n*y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ {R : Type} [Lean.Grind.Semiring R] (x y : R), x*y = y*x := by intros; power_nf
  trivial
