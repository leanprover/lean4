new_frontend

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

theorem aux (a b c : Nat) (h₁ : a = b) (h₂ : c = b) : a = c :=
by {
  let! aux := h₂.symm;
  subst aux;
  subst h₁;
  exact rfl
}

def ex : {α : _} → {a b c : α} → a = b → b = c → a = c :=
@by {
  intro α a b c h₁ h₂;
  exact Eq.trans h₁ h₂
}
