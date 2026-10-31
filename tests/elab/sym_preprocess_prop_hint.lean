/-!
Regression test for `Sym` rewrite and backward rules whose statements are modified by
`Sym.preprocessType` (e.g., unfolding `Unit` to `PUnit` in `match` equation theorems, unfolding
`@[reducible]` definitions, or beta/eta reduction).

Without an expected type hint (`@id`) on the polymorphic rule before instantiating its parameters,
the kernel has to check definitional equality between the un-preprocessed and preprocessed rule
types at the instantiated arguments, which can trigger expensive reduction of `match` discriminants.
-/

def tree : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, k => tree n (2 * k) && tree n (2 * k + 1)

@[cbv_eval] theorem tree_eq_true (n k : Nat) : tree n k = true := by
  induction n generalizing k <;> simp [tree, *]

def viaMatch (n : Nat) : Nat :=
  match tree n 0 with
  | true => 1
  | false => 0

@[reducible] def myId (x : Nat) : Nat := x

def viaRed (n : Nat) : Nat :=
  match tree n 0 with
  | true => myId 1
  | false => 0

@[sym_simp, cbv_eval] private theorem viaRed_eq (n : Nat) :
    viaRed n = match tree n 0 with | true => myId 1 | false => 0 := by
  rfl

def applyFun (f : Nat → Nat) (x : Nat) : Nat := f x

def viaEta (n : Nat) : Nat :=
  match tree n 0 with
  | true => applyFun (fun x => Nat.succ x) 0
  | false => 0

-- 1. `mkTheoremFromDecl` via `Sym.simp` (`Unit` in match equation, reducible unfolding, eta, private `@[sym_simp]`)
theorem matchSym : viaMatch 100 = 1 := by
  sym => simp [viaMatch.eq_1, tree_eq_true]

theorem redSym : viaRed 100 = 1 := by
  sym => simp [tree_eq_true]

theorem etaSym : viaEta 100 = 1 := by
  sym => simp [viaEta.eq_1, applyFun.eq_1, tree_eq_true]

-- 2. `mkTheoremFromDecl` via `cbv` (including `private @[cbv_eval]`)
theorem matchCbv : viaMatch 100 = 1 := by
  cbv

theorem redCbv : viaRed 100 = 1 := by
  cbv

-- 3. `mkTheoremFromExpr` via `Sym.simp` on local hypotheses
theorem matchSymLocal (h : ∀ n, viaMatch n = match tree n 0 with | true => 1 | false => 0) :
    viaMatch 100 = 1 := by
  sym => simp [h, tree_eq_true]

theorem matchSymLocalEta (h : ∀ n, viaMatch ((fun x => x) n) = match tree n 0 with | true => 1 | false => 0) :
    viaMatch 100 = 1 := by
  sym => simp [h, tree_eq_true]

-- 4. Non-equality theorem adapted via `EqAdaptation.eqTrue`
inductive Hold : Nat → Prop where
  | mk (n : Nat) : Hold (match tree n 0 with | true => 1 | false => 0)

theorem hold_thm (n : Nat) : Hold (match tree n 0 with | true => 1 | false => 0) :=
  Hold.mk n

theorem simpProp : Hold (viaMatch 100) := by
  sym => simp [viaMatch.eq_1, hold_thm]

-- 5. `mkBackwardRuleFromDecl` and `mkBackwardRuleFromExpr` via `sym => apply`
theorem applyDecl : Hold (viaMatch 100) := by
  sym =>
    simp [viaMatch.eq_1]
    apply Hold.mk

theorem applyExpr (h : ∀ n, Hold (match tree n 0 with | true => 1 | false => 0)) :
    Hold (viaMatch 100) := by
  sym =>
    simp [viaMatch.eq_1]
    apply h
