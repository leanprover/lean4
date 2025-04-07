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
A functor satisfies the functor laws.

The `Functor` class contains the operations of a functor, but does not require that instances
prove they satisfy the laws of a functor. A `LawfulFunctor` instance includes proofs that the laws
are satisfied. Because `Functor` instances may provide optimized implementations of `mapConst`,
`LawfulFunctor` instances must also prove that the optimized implementation is equivalent to the
standard implementation.
-/
class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  /--
  The `mapConst` implementation is equivalent to the default implementation.
  -/
  map_const          : (Functor.mapConst : α → f β → f α) = Functor.map ∘ const β
  /--
  The `map` implementation preserves identity.
  -/
  id_map   (x : f α) : id <$> x = x
  /--
  The `map` implementation preserves function composition.
  -/
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

export LawfulFunctor (map_const id_map comp_map)

attribute [simp] id_map

@[simp] theorem id_map' [Functor f] [LawfulFunctor f] (x : f α) : (fun a => a) <$> x = x :=
  id_map x

@[simp] theorem Functor.map_map [Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α) :
    g <$> m <$> x = (fun a => g (m a)) <$> x :=
  (comp_map _ _ _).symm

theorem Functor.map_unit [Functor f] [LawfulFunctor f] {a : f PUnit} : (fun _ => PUnit.unit) <$> a = a := by
  simp [map]

/--
An applicative functor satisfies the laws of an applicative functor.

The `Applicative` class contains the operations of an applicative functor, but does not require that
instances prove they satisfy the laws of an applicative functor. A `LawfulApplicative` instance
includes proofs that the laws are satisfied.

Because `Applicative` instances may provide optimized implementations of `seqLeft` and `seqRight`,
`LawfulApplicative` instances must also prove that the optimized implementation is equivalent to the
standard implementation.
-/
class LawfulApplicative (f : Type u → Type v) [Applicative f] : Prop extends LawfulFunctor f where
  /-- `seqLeft` is equivalent to the default implementation. -/
  seqLeft_eq  (x : f α) (y : f β)     : x <* y = const β <$> x <*> y
  /-- `seqRight` is equivalent to the default implementation. -/
  seqRight_eq (x : f α) (y : f β)     : x *> y = const α id <$> x <*> y
  /--
  `pure` before `seq` is equivalent to `Functor.map`.

  This means that `pure` really is pure when occurring immediately prior to `seq`.
   -/
  pure_seq    (g : α → β) (x : f α)   : pure g <*> x = g <$> x

  /--
  Mapping a function over the result of `pure` is equivalent to applying the function under `pure`.

  This means that `pure` really is pure with respect to `Functor.map`.
  -/
  map_pure    (g : α → β) (x : α)     : g <$> (pure x : f α) = pure (g x)

  /--
  `pure` after `seq` is equivalent to `Functor.map`.

  This means that `pure` really is pure when occurring just after `seq`.
  -/
  seq_pure    {α β : Type u} (g : f (α → β)) (x : α) : g <*> pure x = (fun h => h x) <$> g

  /--
  `seq` is associative.

  Changing the nesting of `seq` calls while maintaining the order of computations results in an
  equivalent computation. This means that `seq` is not doing any more than sequencing.
  -/
  seq_assoc   {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = ((@comp α β γ) <$> h) <*> g <*> x
  comp_map g h x := (by
    repeat rw [← pure_seq]
    simp [seq_assoc, map_pure, seq_pure])

export LawfulApplicative (seqLeft_eq seqRight_eq pure_seq map_pure seq_pure seq_assoc)

attribute [simp] map_pure seq_pure

@[simp] theorem pure_id_seq [Applicative f] [LawfulApplicative f] (x : f α) : pure id <*> x = x := by
  simp [pure_seq]

/--
Lawful monads are those that satisfy a certain behavioral specification. While all instances of
`Monad` should satisfy these laws, not all implementations are required to prove this.

`LawfulMonad.mk'` is an alternative constructor that contains useful defaults for many fields.
-/
class LawfulMonad (m : Type u → Type v) [Monad m] : Prop extends LawfulApplicative m where
  /--
  A `bind` followed by `pure` composed with a function is equivalent to a functorial map.

  This means that `pure` really is pure after a `bind` and has no effects.
  -/
  bind_pure_comp (f : α → β) (x : m α) : x >>= (fun a => pure (f a)) = f <$> x
  /--
  A `bind` followed by a functorial map is equivalent to `Applicative` sequencing.

  This means that the effect sequencing from `Monad` and `Applicative` are the same.
  -/
  bind_map       {α β : Type u} (f : m (α → β)) (x : m α) : f >>= (. <$> x) = f <*> x
  /--
  `pure` followed by `bind` is equivalent to function application.

  This means that `pure` really is pure before a `bind` and has no effects.
  -/
  pure_bind      (x : α) (f : α → m β) : pure x >>= f = f x
  /--
  `bind` is associative.

  Changing the nesting of `bind` calls while maintaining the order of computations results in an
  equivalent computation. This means that `bind` is not doing more than data-dependent sequencing.
  -/
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

theorem bind_pure_unit [Monad m] [LawfulMonad m] {x : m PUnit} : (x >>= fun _ => pure ⟨⟩) = x := by
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

/--
This is just a duplicate of `LawfulApplicative.map_pure`,
but sometimes applies when that doesn't.

It is named with a prime to avoid conflict with the inherited field `LawfulMonad.map_pure`.
-/
@[simp] theorem LawfulMonad.map_pure' [Monad m] [LawfulMonad m] {a : α} :
    (f <$> pure a : m β) = pure (f a) := by
  simp only [map_pure]

/--
This is just a duplicate of `Functor.map_map`, but sometimes applies when that doesn't.
-/
@[simp] theorem LawfulMonad.map_map {m} [Monad m] [LawfulMonad m] {x : m α} :
    g <$> f <$> x = (fun a => g (f a)) <$> x := by
  simp only [Functor.map_map]

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
