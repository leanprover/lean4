/-!
Checks the generalization behavior of `fun_induction`.

In particular that it behaves the same as `induction … using ….induct`.
-/

variable (xs ys : List Nat)
variable (P : ∀ {α}, List α → Prop)

-- We re-define this here to avoid stage0 complications
def zipWith (f : α → β → γ) : (xs : List α) → (ys : List β) → List γ
  | x::xs, y::ys => f x y :: zipWith f xs ys
  | _,     _     => []

/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : P (xs✝.zip ys✝)
⊢ P ((x✝ :: xs✝).zip (y✝ :: ys✝))

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
⊢ P (t✝.zip x✝¹)
-/
#guard_msgs in
example : P (List.zip xs ys) := by
  fun_induction zipWith _ xs ys


/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : xs✝.isEmpty = true → P (xs✝.zip ys✝)
h : (x✝ :: xs✝).isEmpty = true
⊢ P ((x✝ :: xs✝).zip (y✝ :: ys✝))

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
h : t✝.isEmpty = true
⊢ P (t✝.zip x✝¹)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  fun_induction zipWith _ xs ys


/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : xs✝.isEmpty = true → P (xs✝.zip ys)
h : (x✝ :: xs✝).isEmpty = true
⊢ P ((x✝ :: xs✝).zip ys)

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
h : t✝.isEmpty = true
⊢ P (t✝.zip ys)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  fun_induction zipWith _ xs (ys.take 2)

/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : xs✝.isEmpty = true → P (xs✝.zip ys)
h : (x✝ :: xs✝).isEmpty = true
⊢ P ((x✝ :: xs✝).zip ys)

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
h : t✝.isEmpty = true
⊢ P (t✝.zip ys)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  induction xs, ys.take 2 using zipWith.induct

/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
h : xs.isEmpty = true
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : P (xs.zip ys✝)
⊢ P (xs.zip (y✝ :: ys✝))

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
h : xs.isEmpty = true
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
⊢ P (xs.zip x✝¹)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  fun_induction zipWith _ (xs.take 2) ys

/--
error: unsolved goals
case case1
xs ys : List Nat
P : {α : Type} → List α → Prop
h : xs.isEmpty = true
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : P (xs.zip ys✝)
⊢ P (xs.zip (y✝ :: ys✝))

case case2
xs ys : List Nat
P : {α : Type} → List α → Prop
h : xs.isEmpty = true
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
⊢ P (xs.zip x✝¹)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  induction xs.take 2, ys using zipWith.induct

/--
error: unsolved goals
case case1
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : ∀ (xs : List Nat), xs.isEmpty = true → P (xs.zip ys✝)
xs : List Nat
h : xs.isEmpty = true
⊢ P (xs.zip (y✝ :: ys✝))

case case2
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
xs : List Nat
h : xs.isEmpty = true
⊢ P (xs.zip x✝¹)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  fun_induction zipWith _ (xs.take 2) ys generalizing xs

/--
error: unsolved goals
case case1
P : {α : Type} → List α → Prop
x✝ : Nat
xs✝ : List Nat
y✝ : Nat
ys✝ : List Nat
ih1✝ : ∀ (xs : List Nat), xs.isEmpty = true → P (xs.zip ys✝)
xs : List Nat
h : xs.isEmpty = true
⊢ P (xs.zip (y✝ :: ys✝))

case case2
P : {α : Type} → List α → Prop
t✝ x✝¹ : List Nat
x✝ : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t✝ = x :: xs → x✝¹ = y :: ys → False
xs : List Nat
h : xs.isEmpty = true
⊢ P (xs.zip x✝¹)
-/
#guard_msgs in
example (h : xs.isEmpty) : P (List.zip xs ys) := by
  induction xs.take 2, ys using zipWith.induct generalizing xs
