universes u v

namespace Experiment1
inductive ArrayLitMatch (α : Type u)
| sz0 {}             : ArrayLitMatch
| sz1 (a₁ : α)       : ArrayLitMatch
| sz2 (a₁ a₂ : α)    : ArrayLitMatch
| sz3 (a₁ a₂ a₃ : α) : ArrayLitMatch
| other {}           : ArrayLitMatch

def matchArrayLit {α : Type u} (a : Array α) : ArrayLitMatch α :=
if a.size = 0 then
  ArrayLitMatch.sz0
else if h : a.size = 1 then
  ArrayLitMatch.sz1 (a.getLit 0 h (ofDecideEqTrue rfl))
else if h : a.size = 2 then
  ArrayLitMatch.sz2 (a.getLit 0 h (ofDecideEqTrue rfl)) (a.getLit 1 h (ofDecideEqTrue rfl))
else if h : a.size = 3 then
  ArrayLitMatch.sz3 (a.getLit 0 h (ofDecideEqTrue rfl)) (a.getLit 1 h (ofDecideEqTrue rfl)) (a.getLit 2 h (ofDecideEqTrue rfl))
else
  ArrayLitMatch.other

def matchArrayLit.eq0 {α : Type u} : matchArrayLit (#[] : Array α) = ArrayLitMatch.sz0 :=
rfl

def matchArrayLit.eq1 {α : Type u} (a₁ : α) : matchArrayLit #[a₁] = ArrayLitMatch.sz1 a₁ :=
rfl

def matchArrayLit.eq2 {α : Type u} (a₁ a₂ : α) : matchArrayLit #[a₁, a₂] = ArrayLitMatch.sz2 a₁ a₂ :=
rfl

def matchArrayLit.eq3 {α : Type u} (a₁ a₂ a₃ : α) : matchArrayLit #[a₁, a₂, a₃] = ArrayLitMatch.sz3 a₁ a₂ a₃ :=
rfl

def matchArrayLit.eq4 {α : Type u} (a₁ a₂ a₃ a₄ : α) : matchArrayLit #[a₁, a₂, a₃, a₄] = ArrayLitMatch.other :=
rfl
end Experiment1

def toListLitAux {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : ∀ (i : Nat), i ≤ a.size → List α → List α
| 0,     hi, acc => acc
| (i+1), hi, acc => toListLitAux i (Nat.leOfSuccLe hi) (a.getLit i hsz (Nat.ltOfLtOfEq (Nat.ltOfLtOfLe (Nat.ltSuccSelf i) hi) hsz) :: acc)

def toArrayLit {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : Array α :=
List.toArray $ toListLitAux a n hsz n (hsz ▸ Nat.leRefl _) []

theorem toArrayLitEq {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : a = toArrayLit a n hsz :=
-- TODO: this is painful to prove without proper automation
sorry
/-
First, we need to prove
∀ i j acc, i ≤ a.size → (toListLitAux a n hsz (i+1) hi acc).index j = if j < i then a.getLit j hsz _ else acc.index (j - i)
by induction

Base case is trivial
(j : Nat) (acc : List α) (hi : 0 ≤ a.size)
     |- (toListLitAux a n hsz 0 hi acc).index j = if j < 0 then a.getLit j hsz _ else acc.index (j - 0)
...  |- acc.index j = acc.index j

Induction

(j : Nat) (acc : List α) (hi : i+1 ≤ a.size)
      |- (toListLitAux a n hsz (i+1) hi acc).index j = if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))
  ... |- (toListLitAux a n hsz i hi' (a.getLit i hsz _ :: acc)).index j = if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))  * by def
  ... |- if j < i     then a.getLit j hsz _ else (a.getLit i hsz _ :: acc).index (j-i)    * by induction hypothesis
         =
         if j < i + 1 then a.getLit j hsz _ else acc.index (j - (i + 1))
If j < i, then both are a.getLit j hsz _
If j = i, then lhs reduces else-branch to (a.getLit i hsz _) and rhs is then-brachn (a.getLit i hsz _)
If j >= i + 1, we use
   - j - i >= 1 > 0
   - (a::as).index k = as.index (k-1) If k > 0
   - j - (i + 1) = (j - i) - 1
   Then lhs = (a.getLit i hsz _ :: acc).index (j-i) = acc.index (j-i-1) = acc.index (j-(i+1)) = rhs

With this proof, we have

∀ j, j < n → (toListLitAux a n hsz n _ []).index j = a.getLit j hsz _

We also need

- (toListLitAux a n hsz n _ []).length = n
- j < n -> (List.toArray as).getLit j _ _ = as.index j

Then using Array.extLit, we have that a = List.toArray $ toListLitAux a n hsz n _ []
-/

theorem Array.eqLitOfSize0 {α : Type u} (a : Array α) (hsz : a.size = 0) : a = #[] :=
toArrayLitEq a 0 hsz
/-
Array.ext a #[] h (fun i h₁ h₂ => absurd h₂ (Nat.notLtZero _))
-/

theorem Array.eqLitOfSize1 {α : Type u} (a : Array α) (hsz : a.size = 1) : a = #[a.getLit 0 hsz (ofDecideEqTrue rfl)] :=
toArrayLitEq a 1 hsz
/-
Array.extLit a #[a.getLit 0 hsz (ofDecideEqTrue rfl)] hsz rfl $ fun i =>
  match i with
  | 0     => fun hi => rfl
  | (n+1) => fun hi =>
    have n < 0 from hi;
    absurd this (Nat.notLtZero _)
-/

theorem Array.eqLitOfSize2 {α : Type u} (a : Array α) (hsz : a.size = 2) : a = #[a.getLit 0 hsz (ofDecideEqTrue rfl), a.getLit 1 hsz (ofDecideEqTrue rfl)] :=
toArrayLitEq a 2 hsz
/-
Array.extLit a #[a.getLit 0 hsz (ofDecideEqTrue rfl), a.getLit 1 hsz (ofDecideEqTrue rfl)] hsz rfl $ fun i =>
  match i with
  | 0     => fun hi => rfl
  | 1     => fun hi => rfl
  | (n+2) => fun hi =>
    have n < 0 from hi;
    absurd this (Nat.notLtZero _)
-/

theorem Array.eqLitOfSize3 {α : Type u} (a : Array α) (hsz : a.size = 3) :
  a = #[a.getLit 0 hsz (ofDecideEqTrue rfl), a.getLit 1 hsz (ofDecideEqTrue rfl), a.getLit 2 hsz (ofDecideEqTrue rfl)] :=
toArrayLitEq a 3 hsz
/-
Array.extLit a #[a.getLit 0 hsz (ofDecideEqTrue rfl), a.getLit 1 hsz (ofDecideEqTrue rfl), a.getLit 2 hsz (ofDecideEqTrue rfl)] hsz rfl $ fun i =>
  match i with
  | 0     => fun hi => rfl
  | 1     => fun hi => rfl
  | 2     => fun hi => rfl
  | (n+3) => fun hi =>
    have n < 0 from hi;
    absurd this (Nat.notLtZero _)
-/

/-
Matcher for the following patterns
```
| #[]           => _
| #[a₁]         => _
| #[a₁, a₂, a₃] => _
| a             => _
``` -/
def matchArrayLit {α : Type u} (C : Array α → Sort v) (a : Array α)
    (h₁ : Unit →      C #[])
    (h₂ : ∀ a₁,       C #[a₁])
    (h₃ : ∀ a₁ a₂ a₃, C #[a₁, a₂, a₃])
    (h₄ : ∀ a,        C a)
    : C a :=
if h : a.size = 0 then
  @Eq.rec _ _ (fun x _ => C x) (h₁ ()) _ (toArrayLitEq a 0 h).symm
else if h : a.size = 1 then
  @Eq.rec _ _ (fun x _ => C x) (h₂ (a.getLit 0 h (ofDecideEqTrue rfl))) _ (toArrayLitEq a 1 h).symm
else if h : a.size = 3 then
  @Eq.rec _ _ (fun x _ => C x) (h₃ (a.getLit 0 h (ofDecideEqTrue rfl)) (a.getLit 1 h (ofDecideEqTrue rfl)) (a.getLit 2 h (ofDecideEqTrue rfl))) _ (toArrayLitEq a 3 h).symm
else
  h₄ a

/- Equational lemmas that should be generated automatically. -/
theorem matchArrayLit.eq1 {α : Type u} (C : Array α → Sort v)
    (h₁ : Unit →      C #[])
    (h₂ : ∀ a₁,       C #[a₁])
    (h₃ : ∀ a₁ a₂ a₃, C #[a₁, a₂, a₃])
    (h₄ : ∀ a,        C a)
    : matchArrayLit C #[] h₁ h₂ h₃ h₄ = h₁ () :=
rfl

theorem matchArrayLit.eq2 {α : Type u} (C : Array α → Sort v)
    (h₁ : Unit →      C #[])
    (h₂ : ∀ a₁,       C #[a₁])
    (h₃ : ∀ a₁ a₂ a₃, C #[a₁, a₂, a₃])
    (h₄ : ∀ a,        C a)
    (a₁ : α)
    : matchArrayLit C #[a₁] h₁ h₂ h₃ h₄ = h₂ a₁ :=
rfl

theorem matchArrayLit.eq3 {α : Type u} (C : Array α → Sort v)
    (h₁ : Unit →      C #[])
    (h₂ : ∀ a₁,       C #[a₁])
    (h₃ : ∀ a₁ a₂ a₃, C #[a₁, a₂, a₃])
    (h₄ : ∀ a,        C a)
    (a₁ a₂ a₃ : α)
    : matchArrayLit C #[a₁, a₂, a₃] h₁ h₂ h₃ h₄ = h₃ a₁ a₂ a₃ :=
rfl

theorem matchArrayLit.eq4 {α : Type u} (C : Array α → Sort v)
    (h₁ : Unit →      C #[])
    (h₂ : ∀ a₁,       C #[a₁])
    (h₃ : ∀ a₁ a₂ a₃, C #[a₁, a₂, a₃])
    (h₄ : ∀ a,        C a)
    (a : Array α)
    (n₁ : a.size ≠ 0) (n₂ : a.size ≠ 1) (n₃ : a.size ≠ 3)
    : matchArrayLit C a h₁ h₂ h₃ h₄ = h₄ a :=
match a, n₁, n₂, n₃ with
| ⟨0, _⟩,   n₁, _, _  => absurd rfl n₁
| ⟨1, _⟩,   _,  n₂, _ => absurd rfl n₂
| ⟨2, _⟩,   _, _, _   => rfl
| ⟨3, _⟩,   _, _, n₃  => absurd rfl n₃
| ⟨n+4, _⟩, _, _, _   => rfl
