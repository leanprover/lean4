new_frontend

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
