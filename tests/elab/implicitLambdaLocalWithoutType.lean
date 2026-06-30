def foo1mk (_ : ∀ (α : Type) (a : α), a = a) : Nat := 37
def foo2mk (_ : ∀ {α : Type} (a : α), a = a) : Nat := 37 -- implicit binder

example (x) : foo1mk x = foo1mk x := rfl -- works
example (x : ∀ {α : Type} (a : α), a = a) : 37 = foo2mk x := rfl -- works
example (x) : 37 = foo2mk @x := rfl -- works
example (x) : foo1mk x = foo1mk x := rfl -- works
example (x : ∀ {α : Type} (a : α), a = a) : foo2mk x = foo2mk x := rfl -- works
example (x) : foo2mk x = foo2mk x := rfl -- works
example (x) : foo2mk x = 37 := rfl -- works
example (x) : foo2mk x = foo2mk x := rfl  -- works

universe u v w

structure ApplicativeTransformation (F : Type u → Type v) [Applicative F] [LawfulApplicative F]
  (G : Type u → Type w) [Applicative G] [LawfulApplicative G] : Type max (u + 1) v w where
  app : ∀ α : Type u, F α → G α
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

variable (G : Type u → Type w) [Applicative G] [LawfulApplicative G]

instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨ApplicativeTransformation.app⟩

variable {F G}

@[simp]
theorem coe_mk (f : ∀ (α : Type u), F α → G α) (pp ps) :
  (ApplicativeTransformation.mk f pp ps) = f :=
  rfl
