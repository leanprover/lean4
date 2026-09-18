/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Basic

universe u v w z
@[expose] public section

set_option linter.missingDocs true

/-!
# Predicate transformers

`PredTrans Pred EPosts α` wraps a map from a normal postcondition `α → Pred` and an exception
postcondition `EPosts` to a precondition `Pred`. The order and the chain-complete suprema are the
pointwise ones of the function space.

`PredTrans Pred EPosts` is a monad, so monadic programs can be interpreted by a monad morphism into
it. This module provides that monad structure, the `apply` simp framework of the monadic
combinators, the `push` family that moves a result type into a postcondition, and the standard
monad class instances.
-/

namespace Lean.Order

/-- A predicate transformer from postconditions to preconditions.

Given a return type `α`, a lattice `Pred` for assertions, and an exception assertion type `EPosts`,
`PredTrans Pred EPosts α` wraps a function `(α → Pred) → EPosts → Pred`. -/
structure PredTrans (Pred : Type u) (EPosts : Type v) (α : Type w) where
  /-- Apply the predicate transformer to a postcondition and exception postcondition. -/
  apply : (α → Pred) → EPosts → Pred

attribute [deprecated_arg EPred EPosts (since := "2026-09-18")] PredTrans

namespace PredTrans

variable {Pred : Type u} {EPosts : Type v} {α β : Type w}

/-- Extensionality for predicate transformers. -/
@[ext] theorem ext {x y : PredTrans Pred EPosts α}
    (h : ∀ post eposts, x.apply post eposts = y.apply post eposts) : x = y := by
  cases x; cases y; congr; funext post eposts; exact h post eposts

/-- Partial order on predicate transformers, inherited from the function space. -/
instance [PartialOrder Pred] : PartialOrder (PredTrans Pred EPosts α) where
  rel x y := x.apply ⊑ y.apply
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm h1 h2 := ext fun post eposts =>
    PartialOrder.rel_antisymm (h1 post eposts) (h2 post eposts)

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. -/
instance [CCPO Pred] : CCPO (PredTrans Pred EPosts α) where
  has_csup {c} hc := by
    let c' : ((α → Pred) → EPosts → Pred) → Prop := fun f => ∃ pt, c pt ∧ pt.apply = f
    have hc' : chain c' := by
      intro _ _ ⟨pf, hpf, hpf_eq⟩ ⟨pg, hpg, hpg_eq⟩
      subst hpf_eq; subst hpg_eq
      exact hc pf pg hpf hpg
    obtain ⟨sup, hsup⟩ := CCPO.has_csup hc'
    refine ⟨⟨sup⟩, fun q => ?_⟩
    constructor
    · intro h pt hpt
      exact (hsup q.apply).mp h pt.apply ⟨pt, hpt, rfl⟩
    · intro h
      exact (hsup q.apply).mpr fun f ⟨pf, hpf, hpf_eq⟩ => by subst hpf_eq; exact h pf hpf

/-- Monotonicity property for a predicate transformer: if both `post` and `eposts` grow,
then the resulting precondition grows. -/
def Monotone [PartialOrder Pred] [PartialOrder EPosts] (pt : PredTrans Pred EPosts α) :=
  ∀ post post' eposts eposts', eposts ⊑ eposts' → post ⊑ post' → pt.apply post eposts ⊑ pt.apply post' eposts'

/-- Conjunctivity property for a predicate transformer: the meet of two preconditions lies below
the precondition of the componentwise meet of the postconditions. -/
def Conjunctive [CompleteLattice Pred] [CompleteLattice EPosts] (pt : PredTrans Pred EPosts α) :=
  ∀ post₁ post₂ eposts₁ eposts₂,
    pt.apply post₁ eposts₁ ⊓ pt.apply post₂ eposts₂ ⊑ pt.apply (post₁ ⊓ post₂) (eposts₁ ⊓ eposts₂)

/-!
## Monad Structure
-/

/-- `pure a` applies the postcondition to `a`. -/
def pure (a : α) : PredTrans Pred EPosts α :=
  ⟨fun post _epost => post a⟩

/-- `bind x f` threads the postcondition through the continuation `f`. -/
def bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β) :
    PredTrans Pred EPosts β :=
  ⟨fun post eposts => x.apply (fun a => (f a).apply post eposts) eposts⟩

instance instMonad : Monad (PredTrans Pred EPosts) where
  pure := pure
  bind := bind

instance instLawfulMonad : LawfulMonad (PredTrans Pred EPosts) where
  map_const := funext fun _ => funext fun _ => ext fun _ _ => rfl
  id_map _ := ext fun _ _ => rfl
  seqLeft_eq _ _ := ext fun _ _ => rfl
  seqRight_eq _ _ := ext fun _ _ => rfl
  pure_seq _ _ := ext fun _ _ => rfl
  bind_pure_comp _ _ := ext fun _ _ => rfl
  bind_map _ _ := ext fun _ _ => rfl
  pure_bind _ _ := ext fun _ _ => rfl
  bind_assoc _ _ _ := ext fun _ _ => rfl

/-!
## `apply_*` simp framework

Simp lemmas for reducing `(expr).apply post eposts` for each monadic combinator.
-/

/-- Unfolding `PredTrans.pure` through `apply`. -/
@[simp, grind =]
theorem apply_pure (a : α) (post : α → Pred) (eposts : EPosts) :
    (PredTrans.pure a : PredTrans Pred EPosts α).apply post eposts = post a := rfl

/-- Unfolding `pure` through `apply`. -/
@[simp, grind =]
theorem apply_Pure_pure (a : α) (post : α → Pred) (eposts : EPosts) :
    (Pure.pure a : PredTrans Pred EPosts α).apply post eposts = post a := rfl

/-- Unfolding `PredTrans.bind` through `apply`. -/
@[simp, grind =]
theorem apply_bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β)
    (post : β → Pred) (eposts : EPosts) :
    (x.bind f).apply post eposts = x.apply (fun a => (f a).apply post eposts) eposts := rfl

/-- Unfolding `>>=` through `apply`. -/
@[simp, grind =]
theorem apply_Bind_bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β)
    (post : β → Pred) (eposts : EPosts) :
    (x >>= f).apply post eposts = x.apply (fun a => (f a).apply post eposts) eposts := rfl

/-- Unfolding `<$>` through `apply`. -/
@[simp, grind =]
theorem apply_Functor_map (f : α → β) (x : PredTrans Pred EPosts α)
    (post : β → Pred) (eposts : EPosts) :
    (f <$> x).apply post eposts = x.apply (post ∘ f) eposts := rfl

/-- Unfolding `<*>` through `apply`. -/
@[simp]
theorem apply_Seq_seq (f : PredTrans Pred EPosts (α → β)) (x : PredTrans Pred EPosts α)
    (post : β → Pred) (eposts : EPosts) :
    (f <*> x).apply post eposts =
      f.apply (fun g => x.apply (fun a => post (g a)) eposts) eposts := rfl

/-- Unfolding `dite` through `apply`. -/
@[simp]
theorem apply_dite (c : Prop) [Decidable c]
    (t : c → PredTrans Pred EPosts α) (e : ¬ c → PredTrans Pred EPosts α)
    (post : α → Pred) (eposts : EPosts) :
    (if h : c then t h else e h).apply post eposts =
      if h : c then (t h).apply post eposts else (e h).apply post eposts := by
  split <;> rfl

/-- Unfolding `ite` through `apply`. -/
@[simp]
theorem apply_ite (c : Prop) [Decidable c]
    (t : PredTrans Pred EPosts α) (e : PredTrans Pred EPosts α)
    (post : α → Pred) (eposts : EPosts) :
    (if c then t else e).apply post eposts =
      if c then t.apply post eposts else e.apply post eposts := by
  split <;> rfl

/-!
## Arguments

Combinators that add or remove a state argument.
-/

/-- Adds a state argument to a predicate transformer.

Given a state-dependent transformer `σ → PredTrans Pred EPosts (α × σ)`, produces a transformer
over `σ → Pred` that threads the state through postconditions. -/
def pushArg {σ : Type z} (x : σ → PredTrans Pred EPosts (α × σ)) :
    PredTrans (σ → Pred) EPosts α :=
  ⟨fun post eposts s => (x s).apply (fun (a, s) => post a s) eposts⟩

/-- Unfolding lemma for `pushArg`: applies the state-threaded transformer at state `s`. -/
@[simp, grind =]
theorem apply_pushArg {σ : Type z} (x : σ → PredTrans Pred EPosts (α × σ))
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (pushArg x).apply post eposts s = (x s).apply (fun (a, s) => post a s) eposts := rfl

/-- Removes the state argument of a predicate transformer by applying it at state `s`.
The transformed result carries the final state. -/
def popArg {σ : Type z} (x : PredTrans (σ → Pred) EPosts α) (s : σ) :
    PredTrans Pred EPosts (α × σ) :=
  ⟨fun post eposts => x.apply (fun a s => post (a, s)) eposts s⟩

/-- Unfolding `popArg` through `apply`. -/
@[simp, grind =]
theorem apply_popArg {σ : Type z} (x : PredTrans (σ → Pred) EPosts α) (s : σ)
    (post : α × σ → Pred) (eposts : EPosts) :
    (x.popArg s).apply post eposts = x.apply (fun a s => post (a, s)) eposts s := rfl

/-- Adds a state argument that the predicate transformer ignores. -/
def liftArg {σ : Type z} (x : PredTrans Pred EPosts α) : PredTrans (σ → Pred) EPosts α :=
  ⟨fun post eposts s => x.apply (fun a => post a s) eposts⟩

/-- Unfolding `liftArg` through `apply`. -/
@[simp, grind =]
theorem apply_liftArg {σ : Type z} (x : PredTrans Pred EPosts α)
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (liftArg x : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = x.apply (fun a => post a s) eposts := rfl

instance {σ : Type z} : MonadLift (PredTrans Pred EPosts) (PredTrans (σ → Pred) EPosts) where
  monadLift := liftArg

/-- Unfolding `monadLift` through `apply`. -/
@[simp, grind =]
theorem apply_monadLift {σ : Type z} (x : PredTrans Pred EPosts α)
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadLift.monadLift x : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = x.apply (fun a => post a s) eposts := rfl

end PredTrans

/-!
## Results

Postconditions for `Except` and `Option` results, and the transformer combinators built on them.
-/

/-- The postcondition for an `Except ε α` result: `ok a` uses `post a`, and `error e` uses
`eposts e`. -/
def pushExcept {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (eposts : ε → Pred) : Except ε α → Pred
  | .ok a => post a
  | .error e => eposts e

/-- A normal result uses the normal postcondition. -/
@[simp, grind =] theorem pushExcept_ok {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (eposts : ε → Pred) (a : α) :
    pushExcept post eposts (.ok a) = post a := rfl

/-- An exceptional result uses the exception postcondition. -/
@[simp, grind =] theorem pushExcept_error {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (eposts : ε → Pred) (e : ε) :
    pushExcept post eposts (.error e) = eposts e := rfl

/-- The postcondition for an `Option α` result: `some a` uses `post a`, and `none` uses
`eposts ()`. -/
def pushOption {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) : Option α → Pred
  | .some a => post a
  | .none => eposts ()

/-- A present result uses the normal postcondition. -/
@[simp, grind =] theorem pushOption_some {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) (a : α) :
    pushOption post eposts (.some a) = post a := rfl

/-- An absent result uses the absent postcondition. -/
@[simp, grind =] theorem pushOption_none {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) :
    pushOption post eposts .none = eposts () := rfl

namespace PredTrans

variable {Pred : Type u} {EPosts : Type v} {α β : Type w}

/-- Adds an exception postcondition layer to a predicate transformer, mirroring `ExceptT`.

Given a transformer over `Except ε α`, produces one over `α` with an additional exception
postcondition for `ε`. The normal and error postconditions are combined via `pushExcept`. -/
def pushExceptT {ε : Type z} (x : PredTrans Pred EPosts (Except ε α)) :
    PredTrans Pred ((ε → Pred) × EPosts) α :=
  ⟨fun post eposts => x.apply (pushExcept post eposts.fst) eposts.snd⟩

/-- Unfolding lemma for `pushExceptT`. -/
@[simp, grind =]
theorem apply_pushExceptT {ε : Type z}
    (x : PredTrans Pred EPosts (Except ε α)) (post : α → Pred)
    (eposts : (ε → Pred) × EPosts) :
    (pushExceptT x).apply post eposts
      = x.apply (pushExcept post eposts.fst) eposts.snd := rfl

/-- Adds an early-termination layer to a predicate transformer, mirroring `OptionT`.

Given a transformer over `Option α`, produces one over `α` with an additional exception
postcondition for the `none` case. -/
def pushOptionT (x : PredTrans Pred EPosts (Option α)) :
    PredTrans Pred ((Unit → Pred) × EPosts) α :=
  ⟨fun post eposts => x.apply (pushOption post eposts.fst) eposts.snd⟩

/-- Unfolding lemma for `pushOptionT`. -/
@[simp, grind =]
theorem apply_pushOptionT (x : PredTrans Pred EPosts (Option α)) (post : α → Pred)
    (eposts : (Unit → Pred) × EPosts) :
    (pushOptionT x).apply post eposts
      = x.apply (pushOption post eposts.fst) eposts.snd := rfl

/-!
## Exception Instances

`throw` and `tryCatch` on the first exception postcondition, and the combinators that lift the
`MonadExceptOf` instance through further layers.
-/

/-- `throw e` asserts the first exception postcondition at `e`. -/
def throw {ε : Type z} (e : ε) : PredTrans Pred ((ε → Pred) × EPosts) α :=
  ⟨fun _post eposts => eposts.fst e⟩

/-- `tryCatch x handle` replaces the first exception postcondition of `x` with the precondition
of the handler. -/
def tryCatch {ε : Type z} (x : PredTrans Pred ((ε → Pred) × EPosts) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPosts) α) :
    PredTrans Pred ((ε → Pred) × EPosts) α :=
  ⟨fun post eposts => x.apply post ((fun e => (handle e).apply post eposts), eposts.snd)⟩

instance {ε : Type z} : MonadExceptOf ε (PredTrans Pred ((ε → Pred) × EPosts)) where
  throw := throw
  tryCatch := tryCatch

/-- Unfolding `throw` through `apply`: the first exception postcondition at the thrown value. -/
@[simp, grind =] theorem apply_throw {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} (e : ε) (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExceptOf.throw e : PredTrans Pred ((ε → Pred) × EPosts) α).apply post eposts
      = eposts.fst e := rfl

/-- Unfolding `tryCatch` through `apply`: the handler replaces the first exception
postcondition. -/
@[simp, grind =] theorem apply_tryCatch {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} (x : PredTrans Pred ((ε → Pred) × EPosts) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPosts) α)
    (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExceptOf.tryCatch x handle).apply post eposts
      = x.apply post ((fun e => (handle e).apply post eposts), eposts.snd) := rfl

/-- Adds a first exception postcondition that the predicate transformer ignores. -/
def liftExcept {eh : Type z} (x : PredTrans Pred EPosts α) : PredTrans Pred (eh × EPosts) α :=
  ⟨fun post eposts => x.apply post eposts.snd⟩

/-- Unfolding `liftExcept` through `apply`. -/
@[simp, grind =]
theorem apply_liftExcept {eh : Type z} (x : PredTrans Pred EPosts α) (post : α → Pred)
    (eposts : eh × EPosts) :
    (liftExcept x : PredTrans Pred (eh × EPosts) α).apply post eposts
      = x.apply post eposts.snd := rfl

/-- Removes the first exception postcondition of a predicate transformer by fixing it to `h`. -/
def popExcept {eh : Type z} (x : PredTrans Pred (eh × EPosts) α) (h : eh) :
    PredTrans Pred EPosts α :=
  ⟨fun post eposts => x.apply post (h, eposts)⟩

/-- Unfolding `popExcept` through `apply`. -/
@[simp, grind =]
theorem apply_popExcept {eh : Type z} (x : PredTrans Pred (eh × EPosts) α) (h : eh)
    (post : α → Pred) (eposts : EPosts) :
    (x.popExcept h).apply post eposts = x.apply post (h, eposts) := rfl

instance {ε : Type u} {Pred : Type v} {EPosts : Type w} {ε' : Type u}
    [MonadExceptOf ε (PredTrans Pred EPosts)] :
    MonadExceptOf ε (PredTrans Pred ((ε' → Pred) × EPosts)) where
  throw e := liftExcept (MonadExceptOf.throw (m := PredTrans Pred EPosts) e)
  tryCatch x handle := ⟨fun post eposts =>
    (MonadExceptOf.tryCatch (m := PredTrans Pred EPosts) (x.popExcept eposts.fst)
      fun e => (handle e).popExcept eposts.fst).apply post eposts.snd⟩

/-!
## State Instances

Standard state and reader class instances for `PredTrans`.
-/

/-- `get` transforms the postcondition into its assertion at the current state. -/
def get {σ : Type z} : PredTrans (σ → Pred) EPosts σ :=
  ⟨fun post _epost s => post s s⟩

/-- `set s'` transforms the postcondition into its assertion at the state `s'`. -/
def set {σ : Type z} (s' : σ) : PredTrans (σ → Pred) EPosts PUnit :=
  ⟨fun post _epost _s => post ⟨⟩ s'⟩

/-- `modifyGet f` transforms the postcondition into its assertion at the result and state
computed by `f`. -/
def modifyGet {σ α : Type z} (f : σ → α × σ) : PredTrans (σ → Pred) EPosts α :=
  ⟨fun post _epost s => post (f s).1 (f s).2⟩

instance {σ : Type z} : MonadStateOf σ (PredTrans (σ → Pred) EPosts) where
  get := get
  set := set
  modifyGet := modifyGet

instance {σ : Type z} : MonadReaderOf σ (PredTrans (σ → Pred) EPosts) where
  read := get

/-- Unfolding `get` through `apply`. -/
@[simp, grind =] theorem apply_get {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.get : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := rfl

/-- Unfolding `set` through `apply`. -/
@[simp, grind =] theorem apply_set {σ : Type z}
    (s' : σ) (post : PUnit → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.set s' : PredTrans (σ → Pred) EPosts PUnit).apply post eposts s = post ⟨⟩ s' := rfl

/-- Unfolding `modifyGet` through `apply`. -/
@[simp, grind =] theorem apply_modifyGet {σ α : Type z}
    (f : σ → α × σ) (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.modifyGet f : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = post (f s).1 (f s).2 := rfl

/-- Unfolding `read` through `apply`. -/
@[simp, grind =] theorem apply_read {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadReaderOf.read : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := rfl

instance {ε : Type u'} {σ : Type z} [MonadExceptOf ε (PredTrans Pred EPosts)] :
    MonadExceptOf ε (PredTrans (σ → Pred) EPosts) where
  throw e := liftArg (MonadExceptOf.throw (m := PredTrans Pred EPosts) e)
  tryCatch x handle := pushArg fun s =>
    MonadExceptOf.tryCatch (m := PredTrans Pred EPosts) (x.popArg s) fun e => (handle e).popArg s

end PredTrans

end Lean.Order

end -- public section
