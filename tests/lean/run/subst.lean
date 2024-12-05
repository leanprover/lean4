universe u

def f1 (n m : Nat) (x : Fin n) (h : n = m) : Fin m :=
h ▸ x

def f2 (n m : Nat) (x : Fin n) (h : m = n) : Fin m :=
h ▸ x

theorem ex1 {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
h₂ ▸ h₁

theorem ex2 {α : Sort u} {a b : α} (h : a = b) : b = a :=
h ▸ rfl

theorem ex3 {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂ ▸ h₁

theorem ex3b {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂.symm ▸ h₁

theorem ex3c {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
h₂.symm.symm ▸ h₁

theorem ex4 {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
h₁ ▸ h₂

theorem ex5 {p : Prop} (h : p = True) : p :=
h ▸ trivial

theorem ex6 {p : Prop} (h : p = False) : ¬p :=
fun hp => h ▸ hp

theorem ex7 {α} {a b c d : α} (h₁ : a = c) (h₂ : b = d) (h₃ : c ≠ d) : a ≠ b :=
h₁ ▸ h₂ ▸ h₃

theorem ex8 (n m k : Nat) (h : Nat.succ n + m = Nat.succ n + k) : Nat.succ (n + m) = Nat.succ (n + k) :=
Nat.succ_add .. ▸ Nat.succ_add .. ▸ h

theorem ex9 (a b : Nat) (h₁ : a = a + b) (h₂ : a = b) : a = b + a  :=
h₂ ▸ h₁

theorem ex10 (a b : Nat) (h : a = b) : b = a :=
h ▸ rfl

def ex11  {α : Type u} {n : Nat} (a : Array α) (i : Nat) (h₁ : a.size = n) (h₂ : i < n) : α :=
  a[i]

theorem ex12 {α : Type u} {n : Nat}
  (a b : Array α)
  (hsz₁ : a.size = n) (hsz₂ : b.size = n)
  (h : ∀ (i : Nat) (hi : i < n), a.getLit i hsz₁ hi = b.getLit i hsz₂ hi) : a = b :=
Array.ext a b (hsz₁.trans hsz₂.symm) fun i hi₁ hi₂ => h i (hsz₁ ▸ hi₁)

def toArrayLit {α : Type u} (a : Array α) (n : Nat) (hsz : a.size = n) : Array α :=
List.toArray $ Array.toListLitAux a n hsz n (hsz ▸ Nat.le_refl _) []

partial def isEqvAux {α} (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) (i : Nat) : Bool :=
  if h : i < a.size then
     let aidx : Fin a.size := ⟨i, h⟩
     let bidx : Fin b.size := ⟨i, hsz ▸ h⟩
     match p a[aidx] b[bidx] with
     | true  => isEqvAux a b hsz p (i+1)
     | false => false
  else
    true
