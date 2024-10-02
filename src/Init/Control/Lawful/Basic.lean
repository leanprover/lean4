/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.SimpLemmas
import Init.Meta

open Function

@[simp] theorem monadLift_self {m : Type u → Type v} (x : m α) : monadLift x = x :=
  rfl

/--
The `Functor` typeclass only contains the operations of a functor.
`LawfulFunctor` further asserts that these operations satisfy the laws of a functor,
including the preservation of the identity and composition laws:
```
id <$> x = x
(h ∘ g) <$> x = h <$> g <$> x
```
-/
class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const          : (Functor.mapConst : α → f β → f α) = Functor.map ∘ const β
  id_map   (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

export LawfulFunctor (map_const id_map comp_map)

attribute [simp] id_map

@[simp] theorem id_map' [Functor m] [LawfulFunctor m] (x : m α) : (fun a => a) <$> x = x :=
  id_map x

@[simp] theorem Functor.map_map [Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α) :
    g <$> m <$> x = (fun a => g (m a)) <$> x :=
  (comp_map _ _ _).symm

/--
The `Applicative` typeclass only contains the operations of an applicative functor.
`LawfulApplicative` further asserts that these operations satisfy the laws of an applicative functor:
```
pure id <*> v = v
pure (·∘·) <*> u <*> v <*> w = u <*> (v <*> w)
pure f <*> pure x = pure (f x)
u <*> pure y = pure (· y) <*> u
```
-/
class LawfulApplicative (f : Type u → Type v) [Applicative f] extends LawfulFunctor f : Prop where
  seqLeft_eq  (x : f α) (y : f β)     : x <* y = const β <$> x <*> y
  seqRight_eq (x : f α) (y : f β)     : x *> y = const α id <$> x <*> y
  pure_seq    (g : α → β) (x : f α)   : pure g <*> x = g <$> x
  map_pure    (g : α → β) (x : α)     : g <$> (pure x : f α) = pure (g x)
  seq_pure    {α β : Type u} (g : f (α → β)) (x : α) : g <*> pure x = (fun h => h x) <$> g
  seq_assoc   {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = ((@comp α β γ) <$> h) <*> g <*> x
  comp_map g h x := (by
    repeat rw [← pure_seq]
    simp [seq_assoc, map_pure, seq_pure])

export LawfulApplicative (seqLeft_eq seqRight_eq pure_seq map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

@[simp] theorem pure_id_seq [Applicative f] [LawfulApplicative f] (x : f α) : pure id <*> x = x := by
  simp [pure_seq]

/--
The `Monad` typeclass only contains the operations of a monad.
`LawfulMonad` further asserts that these operations satisfy the laws of a monad,
including associativity and identity laws for `bind`:
```
pure x >>= f = f x
x >>= pure = x
x >>= f >>= g = x >>= (fun x => f x >>= g)
```

`LawfulMonad.mk'` is an alternative constructor containing useful defaults for many fields.
-/
class LawfulMonad (m : Type u → Type v) [Monad m] extends LawfulApplicative m : Prop where
  bind_pure_comp (f : α → β) (x : m α) : x >>= (fun a => pure (f a)) = f <$> x
  bind_map       {α β : Type u} (f : m (α → β)) (x : m α) : f >>= (. <$> x) = f <*> x
  pure_bind      (x : α) (f : α → m β) : pure x >>= f = f x
  bind_assoc     (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun x => f x >>= g
  map_pure g x    := (by rw [← bind_pure_comp, pure_bind])
  seq_pure g x    := (by rw [← bind_map]; simp [map_pure, bind_pure_comp])
  seq_assoc x g h := (by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind])

export LawfulMonad (bind_pure_comp bind_map pure_bind bind_assoc)
attribute [simp] pure_bind bind_assoc bind_pure_comp

@[simp] theorem bind_pure [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x := by
  show x >>= (fun a => pure (id a)) = x
  rw [bind_pure_comp, id_map]

/--
Use `simp [← bind_pure_comp]` rather than `simp [map_eq_pure_bind]`,
as `bind_pure_comp` is in the default simp set, so also using `map_eq_pure_bind` would cause a loop.
-/
theorem map_eq_pure_bind [Monad m] [LawfulMonad m] (f : α → β) (x : m α) : f <$> x = x >>= fun a => pure (f a) := by
  rw [← bind_pure_comp]

theorem seq_eq_bind_map {α β : Type u} [Monad m] [LawfulMonad m] (f : m (α → β)) (x : m α) : f <*> x = f >>= (. <$> x) := by
  rw [← bind_map]

theorem bind_congr [Bind m] {x : m α} {f g : α → m β} (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  simp [funext h]

@[simp] theorem bind_pure_unit [Monad m] [LawfulMonad m] {x : m PUnit} : (x >>= fun _ => pure ⟨⟩) = x := by
  rw [bind_pure]

theorem map_congr [Functor m] {x : m α} {f g : α → β} (h : ∀ a, f a = g a) : (f <$> x : m β) = g <$> x := by
  simp [funext h]

theorem seq_eq_bind {α β : Type u} [Monad m] [LawfulMonad m] (mf : m (α → β)) (x : m α) : mf <*> x = mf >>= fun f => f <$> x := by
  rw [bind_map]

theorem seqRight_eq_bind [Monad m] [LawfulMonad m] (x : m α) (y : m β) : x *> y = x >>= fun _ => y := by
  rw [seqRight_eq]
  simp only [map_eq_pure_bind, const, seq_eq_bind_map, bind_assoc, pure_bind, id_eq, bind_pure]

theorem seqLeft_eq_bind [Monad m] [LawfulMonad m] (x : m α) (y : m β) : x <* y = x >>= fun a => y >>= fun _ => pure a := by
  rw [seqLeft_eq]
  simp only [map_eq_pure_bind, seq_eq_bind_map, bind_assoc, pure_bind, const_apply]

@[simp] theorem map_bind [Monad m] [LawfulMonad m] (f : β → γ) (x : m α) (g : α → m β) :
    f <$> (x >>= g) = x >>= fun a => f <$> g a := by
  rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  simp [bind_pure_comp]

@[simp] theorem bind_map_left [Monad m] [LawfulMonad m] (f : α → β) (x : m α) (g : β → m γ) :
    ((f <$> x) >>= fun b => g b) = (x >>= fun a => g (f a)) := by
  rw [← bind_pure_comp]
  simp only [bind_assoc, pure_bind]

@[simp] theorem Functor.map_unit [Monad m] [LawfulMonad m] {a : m PUnit} : (fun _ => PUnit.unit) <$> a = a := by
  simp [map]

/--
An alternative constructor for `LawfulMonad` which has more
defaultable fields in the common case.
-/
theorem LawfulMonad.mk' (m : Type u → Type v) [Monad m]
    (id_map : ∀ {α} (x : m α), id <$> x = x)
    (pure_bind : ∀ {α β} (x : α) (f : α → m β), pure x >>= f = f x)
    (bind_assoc : ∀ {α β γ} (x : m α) (f : α → m β) (g : β → m γ),
      x >>= f >>= g = x >>= fun x => f x >>= g)
    (map_const : ∀ {α β} (x : α) (y : m β),
      Functor.mapConst x y = Function.const β x <$> y := by intros; rfl)
    (seqLeft_eq : ∀ {α β} (x : m α) (y : m β),
      x <* y = (x >>= fun a => y >>= fun _ => pure a) := by intros; rfl)
    (seqRight_eq : ∀ {α β} (x : m α) (y : m β), x *> y = (x >>= fun _ => y) := by intros; rfl)
    (bind_pure_comp : ∀ {α β} (f : α → β) (x : m α),
      x >>= (fun y => pure (f y)) = f <$> x := by intros; rfl)
    (bind_map : ∀ {α β} (f : m (α → β)) (x : m α), f >>= (. <$> x) = f <*> x := by intros; rfl)
    : LawfulMonad m :=
  have map_pure {α β} (g : α → β) (x : α) : g <$> (pure x : m α) = pure (g x) := by
    rw [← bind_pure_comp]; simp [pure_bind]
  { id_map, bind_pure_comp, bind_map, pure_bind, bind_assoc, map_pure,
    comp_map := by simp [← bind_pure_comp, bind_assoc, pure_bind]
    pure_seq := by intros; rw [← bind_map]; simp [pure_bind]
    seq_pure := by intros; rw [← bind_map]; simp [map_pure, bind_pure_comp]
    seq_assoc := by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind]
    map_const := funext fun x => funext (map_const x)
    seqLeft_eq := by simp [seqLeft_eq, ← bind_map, ← bind_pure_comp, pure_bind, bind_assoc]
    seqRight_eq := fun x y => by
      rw [seqRight_eq, ← bind_map, ← bind_pure_comp, bind_assoc]; simp [pure_bind, id_map] }

/-! # Id -/

namespace Id

@[simp] theorem map_eq (x : Id α) (f : α → β) : f <$> x = f x := rfl
@[simp] theorem bind_eq (x : Id α) (f : α → id β) : x >>= f = f x := rfl
@[simp] theorem pure_eq (a : α) : (pure a : Id α) = a := rfl

instance : LawfulMonad Id := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> intros <;> rfl

end Id

/-! # Option -/

instance : LawfulMonad Option := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)
  (bind_pure_comp := fun _ x => by cases x <;> rfl)

instance : LawfulApplicative Option := inferInstance
instance : LawfulFunctor Option := inferInstance
