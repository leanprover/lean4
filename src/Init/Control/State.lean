/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer.
-/
prelude
import Init.Control.Alternative
import Init.Control.Lift
import Init.Control.Id
import Init.Control.Except
universes u v w

def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
σ → m (α × σ)

@[inline] def StateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : StateT σ m α) (s : σ) : m (α × σ) :=
x s

@[inline] def StateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
Prod.fst <$> x s

@[reducible] def StateM (σ α : Type u) : Type u := StateT σ Id α

instance StateM.subsingleton {σ α} [Subsingleton σ] [Subsingleton α] : Subsingleton (StateM σ α) :=
⟨λ x y => funext $ fun (s : σ) => match x s, y s with
  | (a₁, s₁), (a₂, s₂) => Subsingleton.elim a₁ a₂ ▸ Subsingleton.elim s₁ s₂ ▸ rfl⟩

namespace StateT
section
variables {σ : Type u} {m : Type u → Type v}
variables [Monad m] {α β : Type u}

@[inline] protected def pure (a : α) : StateT σ m α :=
fun s => pure (a, s)

@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
fun s => do (a, s) ← x s; f a s

@[inline] protected def map (f : α → β) (x : StateT σ m α) : StateT σ m β :=
fun s => do (a, s) ← x s; pure (f a, s)

instance : Monad (StateT σ m) :=
{ pure := @StateT.pure _ _ _, bind := @StateT.bind _ _ _, map := @StateT.map _ _ _ }

@[inline] protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
fun s => failure

instance [Alternative m] : Alternative (StateT σ m) :=
{ StateT.Monad with
  failure := @StateT.failure _ _ _ _,
  orelse  := @StateT.orelse _ _ _ _ }

@[inline] protected def get : StateT σ m σ :=
fun s => pure (s, s)

@[inline] protected def set : σ → StateT σ m PUnit :=
fun s' s => pure (⟨⟩, s')

@[inline] protected def modifyGet (f : σ → α × σ) : StateT σ m α :=
fun s => pure (f s)

@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
fun s => do a ← t; pure (a, s)

instance : HasMonadLift m (StateT σ m) :=
⟨@StateT.lift σ m _⟩

instance (σ m m') [Monad m] [Monad m'] : MonadFunctor m m' (StateT σ m) (StateT σ m') :=
⟨fun _ f x s => f (x s)⟩

@[inline] protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [Monad m] (split : σ → σ' × σ'')
        (join : σ' → σ'' → σ) (x : StateT σ' m α) : StateT σ m α :=
fun st => do
  let (st, ctx) := split st;
  (a, st') ← x st;
  pure (a, join st' ctx)

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateT σ m) :=
{ throw := fun α => StateT.lift ∘ throwThe ε,
  catch := fun α x c s => catchThe ε (x s) (fun e => c e s) }

end
end StateT

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadStateOf (σ : Type u) (m : Type u → Type v) :=
/- Obtain the top-most State of a Monad stack. -/
(get : m σ)
/- Set the top-most State of a Monad stack. -/
(set : σ → m PUnit)
/- Map the top-most State of a Monad stack.

   Note: `modifyGet f` may be preferable to `do s <- get; let (a, s) := f s; put s; pure a`
   because the latter does not use the State linearly (without sufficient inlining). -/
(modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadStateOf (set)

abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
MonadStateOf.get

@[inline] abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

@[inline] abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → α × σ) : m α :=
MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an outParam for convenience -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :=
(get : m σ)
(set : σ → m PUnit)
(modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadState (get modifyGet)

instance monadStateOf.isMonadState (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m :=
{ set       := MonadStateOf.set,
  get       := getThe σ,
  modifyGet := fun α f => MonadStateOf.modifyGet f }

section
variables {σ : Type u} {m : Type u → Type v}

@[inline] def modify [MonadState σ m] (f : σ → σ) : m PUnit :=
modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify [MonadState σ m] [Monad m] (f : σ → σ) : m σ := do
modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance monadStateTrans {n : Type u → Type w} [MonadStateOf σ m] [HasMonadLift m n] : MonadStateOf σ n :=
{ get       := monadLift (MonadStateOf.get : m _),
  set       := fun st => monadLift (MonadStateOf.set st : m _),
  modifyGet := fun α f => monadLift (MonadState.modifyGet f : m _) }

instance [Monad m] : MonadStateOf σ (StateT σ m) :=
{ get := StateT.get,
  set := StateT.set,
  modifyGet := @StateT.modifyGet _ _ _ }

end

/-- Adapt a Monad stack, changing the Type of its top-most State.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `MonadFunctor`.

    For zooming into a part of the State, the `split` Function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer State (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the State will not be used linearly in this case.

    Example:
    ```
    def zoomFst {α σ σ' : Type} : State σ α → State (σ × σ') α :=
    adaptState id Prod.mk
    ```

    The Function can also zoom out into a "larger" State, where the new parts are supplied by `split` and discarded by `join` in the end. The State is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def withSnd {α σ σ' : Type} (snd : σ') : State (σ × σ') α → State σ α :=
    adaptState (fun st => ((st, snd), ())) (fun ⟨st,snd⟩ _ => st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadStateFunctor (σ σ' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [Monad m], StateT σ m α → StateT σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `StateT` anywhere in the Monad stack".
    If we look at the unfolded Type of the first argument `∀ m [Monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens Type `∀ f [Functor f], (α → f α) → β → f β` with `f` specialized to `fun σ => m (α × σ)` (exercise: show that this is a lawful Functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    fun f _ st => let (st, ctx) := split st in
              (fun st' => join st' ctx) <$> f st
    ```
    -/
class MonadStateAdapter (σ σ' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptState {σ'' α : Type u} (split : σ' → σ × σ'') (join : σ → σ'' → σ') : m α → m' α)
export MonadStateAdapter (adaptState)

section
variables {σ σ' : Type u} {m m' : Type u → Type v}

@[inline] def MonadStateAdapter.adaptState' [MonadStateAdapter σ σ' m m'] {α : Type u} (toSigma : σ' → σ) (fromSigma : σ → σ') : m α → m' α :=
adaptState (fun st => (toSigma st, PUnit.unit)) (fun st _ => fromSigma st)
export MonadStateAdapter (adaptState')

instance monadStateAdapterTrans {n n' : Type u → Type v} [MonadStateAdapter σ σ' m m'] [MonadFunctor m m' n n'] : MonadStateAdapter σ σ' n n' :=
⟨fun σ'' α split join => monadMap (fun α => (adaptState split join : m α → m' α))⟩

instance [Monad m] : MonadStateAdapter σ σ' (StateT σ m) (StateT σ' m) :=
⟨fun σ'' α => StateT.adapt⟩
end

instance (σ : Type u) (m out : Type u → Type v) [MonadRun out m] [Functor m] : MonadRun (fun α => σ → out α) (StateT σ m) :=
⟨fun α x => run ∘ StateT.run' x⟩

class MonadStateRunner (σ : Type u) (m m' : Type u → Type u) :=
(runState {α : Type u} : m α → σ → m' α)
export MonadStateRunner (runState)

section
variables {σ σ' : Type u} {m m' : Type u → Type u}

instance monadStateRunnerTrans {n n' : Type u → Type u} [MonadStateRunner σ m m'] [MonadFunctor m m' n n'] : MonadStateRunner σ n n' :=
⟨fun α x s => monadMap (fun (α) (y : m α) => (runState y s : m' α)) x⟩

instance StateT.MonadStateRunner [Monad m] : MonadStateRunner σ (StateT σ m) m :=
⟨fun α x s => Prod.fst <$> x s⟩
end
