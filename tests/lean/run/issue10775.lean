set_option linter.unusedVariables false

opaque R : (n m : Int) → Type

axiom mkR : Nat → R n m

noncomputable def d : ∀ (n m : Int), R n m
  | .ofNat n, .ofNat m => mkR 0
  | .negSucc n, .negSucc m => mkR 0
  | .negSucc 0, .ofNat 0 => mkR 0
  | .ofNat _, .negSucc _ => mkR 0
  | .negSucc _, .ofNat _ => mkR 0

/--
error: unsolved goals
case refine_1
⊢ ∀ (n m : Nat), ¬↑n + 1 = ↑m → mkR 0 = mkR 0

case refine_2
⊢ ∀ (n m : Nat), ¬Int.negSucc n + 1 = Int.negSucc m → mkR 0 = mkR 0

case refine_3
⊢ ¬0 = 0 → mkR 0 = mkR 0

case refine_4
⊢ ∀ (a a_1 : Nat), ¬↑a + 1 = Int.negSucc a_1 → mkR 0 = mkR 0

case refine_5
⊢ ∀ (a a_1 : Nat), (a = 0 → a_1 = 0 → False) → ¬Int.negSucc a + 1 = ↑a_1 → mkR 0 = mkR 0
-/
#guard_msgs in
example : (n m : Int) → (hnm : n + 1 ≠ m) → d n m = mkR 0 := by
  refine d.fun_cases_unfolding (motive := fun n m r => (n + 1 ≠ m) → r = mkR 0)
    ?_ ?_ ?_ ?_ ?_ <;> dsimp

/--
error: unsolved goals
case case1
n✝ m✝ : Nat
hnm : Int.ofNat n✝ + 1 ≠ Int.ofNat m✝
⊢ d (Int.ofNat n✝) (Int.ofNat m✝) = mkR 0

case case2
n✝ m✝ : Nat
hnm : Int.negSucc n✝ + 1 ≠ Int.negSucc m✝
⊢ d (Int.negSucc n✝) (Int.negSucc m✝) = mkR 0

case case3
hnm : Int.negSucc 0 + 1 ≠ Int.ofNat 0
⊢ d (Int.negSucc 0) (Int.ofNat 0) = mkR 0

case case4
a✝¹ a✝ : Nat
hnm : Int.ofNat a✝¹ + 1 ≠ Int.negSucc a✝
⊢ d (Int.ofNat a✝¹) (Int.negSucc a✝) = mkR 0

case case5
a✝¹ a✝ : Nat
x✝ : a✝¹ = 0 → a✝ = 0 → False
hnm : Int.negSucc a✝¹ + 1 ≠ Int.ofNat a✝
⊢ d (Int.negSucc a✝¹) (Int.ofNat a✝) = mkR 0
-/
#guard_msgs in
example : (n m : Int) → (hnm : n + 1 ≠ m) → d n m = mkR 0 := by
  intros n m hnm
  fun_cases d

-- set_option trace.Elab.induction true in

/--
error: unsolved goals
case case1
n✝ m✝ : Nat
hnm : Int.ofNat n✝ + 1 ≠ Int.ofNat m✝
⊢ d (Int.ofNat n✝) (Int.ofNat m✝) = mkR 0

case case2
n✝ m✝ : Nat
hnm : Int.negSucc n✝ + 1 ≠ Int.negSucc m✝
⊢ d (Int.negSucc n✝) (Int.negSucc m✝) = mkR 0

case case3
hnm : Int.negSucc 0 + 1 ≠ Int.ofNat 0
⊢ d (Int.negSucc 0) (Int.ofNat 0) = mkR 0

case case4
a✝¹ a✝ : Nat
hnm : Int.ofNat a✝¹ + 1 ≠ Int.negSucc a✝
⊢ d (Int.ofNat a✝¹) (Int.negSucc a✝) = mkR 0

case case5
a✝¹ a✝ : Nat
x✝ : a✝¹ = 0 → a✝ = 0 → False
hnm : Int.negSucc a✝¹ + 1 ≠ Int.ofNat a✝
⊢ d (Int.negSucc a✝¹) (Int.ofNat a✝) = mkR 0
-/
#guard_msgs(pass trace, all) in
example : (n m : Int) → (hnm : n + 1 ≠ m) → d n m = mkR 0 := by
  intros n m hnm
  cases n, m using d.fun_cases_unfolding

/--
error: unsolved goals
case case1
n✝ m✝ : Nat
hnm : Int.ofNat n✝ + 1 ≠ Int.ofNat m✝
⊢ mkR 0 = mkR 0

case case2
n✝ m✝ : Nat
hnm : Int.negSucc n✝ + 1 ≠ Int.negSucc m✝
⊢ mkR 0 = mkR 0

case case3
hnm : Int.negSucc 0 + 1 ≠ Int.ofNat 0
⊢ mkR 0 = mkR 0

case case4
a✝¹ a✝ : Nat
hnm : Int.ofNat a✝¹ + 1 ≠ Int.negSucc a✝
⊢ mkR 0 = mkR 0

case case5
a✝¹ a✝ : Nat
x✝ : a✝¹ = 0 → a✝ = 0 → False
hnm : Int.negSucc a✝¹ + 1 ≠ Int.ofNat a✝
⊢ mkR 0 = mkR 0
-/
#guard_msgs(pass trace, all) in
example : (n m : Int) → (hnm : n + 1 ≠ m) → d n m = mkR 0 := by
  intros n m hnm
  induction n, m using d.fun_cases_unfolding
