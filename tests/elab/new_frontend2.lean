declare_syntax_cat foo

variable {m : Type → Type}
variable [s : Functor m]

#check @Nat.rec

#check s.map

/-
The following doesn't work because
```
variable [r : Monad m]
#check r.map
```
because `Monad.to* methods have bad binder annotations
-/

theorem aux (a b c : Nat) (h₁ : a = b) (h₂ : c = b) : a = c := by
  have aux := h₂.symm
  subst aux
  subst h₁
  exact rfl


def ex1 : {α : Type} → {a b c : α} → a = b → b = c → a = c :=
  @(by intro α a b c h₁ h₂
       exact Eq.trans h₁ h₂)

def f1 (x : Nat) : Nat := by
  apply (· + ?hole)
  exact 1
  case hole => exact x

theorem ex2 (x : Nat) : f1 x = 1 + x :=
rfl

def f2 (x : Nat) : Nat := by
  apply Nat.add _
  exact 1
  exact x

theorem ex3 (x : Nat) : f2 x = x + 1 :=
  rfl
