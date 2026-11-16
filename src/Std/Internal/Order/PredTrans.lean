/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Order.Basic

universe u v w z
public section

set_option linter.missingDocs true

/-!
# Predicate transformers

`PredTrans Pred EPosts α` wraps a map from a normal postcondition `α → Pred` and an exception
postcondition `EPosts` to a precondition `Pred`. The order and the chain-complete suprema are the
pointwise ones of the function space.

`PredTrans Pred EPosts` is a monad, so monadic programs can be interpreted by a monad morphism into
it. This module provides that monad structure, the `apply` computation rules of the monadic
combinators, the `push` family that moves a result type into a postcondition, and the standard
monad class instances.
-/

namespace Lean.Order

/-- A monotone predicate transformer from postconditions to preconditions.

Given a return type `α`, an ordered type `Pred` of assertions, and an ordered type `EPosts` of
exception postconditions, `PredTrans Pred EPosts α` is a function `(α → Pred) → EPosts → Pred`
that is monotone in both arguments. `PredTrans.mk` builds one, `PredTrans.apply` applies it, and
`PredTrans.apply_mono` states its monotonicity. -/
structure PredTrans (Pred : Type u) (EPosts : Type v) [PartialOrder Pred] [PartialOrder EPosts]
    (α : Type w) where
  private mkRaw ::
  private applyRaw : (α → Pred) → EPosts → Pred
  private applyRaw_mono : ∀ {post post' : α → Pred} {eposts eposts' : EPosts},
    post ⊑ post' → eposts ⊑ eposts' → applyRaw post eposts ⊑ applyRaw post' eposts'

attribute [deprecated_arg EPred EPosts (since := "2026-09-18")] PredTrans

namespace PredTrans

variable {Pred : Type u} {EPosts : Type v} [PartialOrder Pred] [PartialOrder EPosts] {α : Type w}

/-- Apply the predicate transformer to a postcondition and exception postcondition. -/
-- A semireducible wrapper over the structure field, so that the kernel unfolds it lazily.
def apply (t : PredTrans Pred EPosts α) (post : α → Pred) (eposts : EPosts) : Pred :=
  t.applyRaw post eposts

/-- Larger postconditions give a larger precondition. -/
theorem apply_mono (t : PredTrans Pred EPosts α) {post post' : α → Pred}
    {eposts eposts' : EPosts} :
    post ⊑ post' → eposts ⊑ eposts' → t.apply post eposts ⊑ t.apply post' eposts' :=
  t.applyRaw_mono

/-- The predicate transformer with the monotone function `apply`. -/
-- The orders are implicit, so that they come from the expected type. Then `apply` and `mk` carry
-- the same order terms, and `apply_mk` rewrites.
def mk {Pred : Type u} {EPosts : Type v} {_ : PartialOrder Pred} {_ : PartialOrder EPosts}
    (apply : (α → Pred) → EPosts → Pred)
    (apply_mono : ∀ {post post' : α → Pred} {eposts eposts' : EPosts},
      post ⊑ post' → eposts ⊑ eposts' → apply post eposts ⊑ apply post' eposts') :
    PredTrans Pred EPosts α :=
  ⟨apply, apply_mono⟩

@[simp, grind norm] theorem apply_mk {Pred : Type u} {EPosts : Type v} {_ : PartialOrder Pred}
    {_ : PartialOrder EPosts} (f : (α → Pred) → EPosts → Pred)
    (h : ∀ {post post' : α → Pred} {eposts eposts' : EPosts},
      post ⊑ post' → eposts ⊑ eposts' → f post eposts ⊑ f post' eposts') :
    (mk f @h).apply = f := (rfl)

/-- Extensionality for predicate transformers. -/
@[ext] theorem ext {t₁ t₂ : PredTrans Pred EPosts α}
    (h : ∀ post eposts, t₁.apply post eposts = t₂.apply post eposts) : t₁ = t₂ := by
  cases t₁; cases t₂; congr; funext post eposts; exact h post eposts

end PredTrans

end Lean.Order

end

@[expose] public section

namespace Lean.Order

namespace PredTrans

variable {Pred : Type u} {EPosts : Type v} [PartialOrder Pred] [PartialOrder EPosts] {α β : Type w}

/-- Partial order on predicate transformers, inherited from the function space. -/
instance : PartialOrder (PredTrans Pred EPosts α) where
  rel x y := x.apply ⊑ y.apply
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm h1 h2 := ext fun post eposts =>
    PartialOrder.rel_antisymm (h1 post eposts) (h2 post eposts)

/-- The values at `post` and `eposts` of the transformers in `c` form a chain. -/
theorem chain_apply {Pred : Type u} [CCPO Pred] {c : PredTrans Pred EPosts α → Prop}
    (hc : chain c) (post : α → Pred) (eposts : EPosts) :
    chain (fun p => ∃ pt, c pt ∧ pt.apply post eposts = p) := by
  intro _ _ ⟨pt₁, h₁, hp₁⟩ ⟨pt₂, h₂, hp₂⟩
  subst hp₁; subst hp₂
  cases hc pt₁ pt₂ h₁ h₂
  next h => exact .inl (h post eposts)
  next h => exact .inr (h post eposts)

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. The
supremum of a chain is pointwise. -/
instance {Pred : Type u} [CCPO Pred] : CCPO (PredTrans Pred EPosts α) where
  has_csup {c} hc := by
    refine ⟨mk (fun post eposts => CCPO.csup (chain_apply hc post eposts))
    (?_), fun q => ?_⟩
    · intro post post' eposts eposts' hpost heposts
      refine csup_le (chain_apply hc post eposts) fun p ⟨pt, hpt, hp⟩ => ?_
      subst hp
      exact PartialOrder.rel_trans (pt.apply_mono hpost heposts)
        (le_csup (chain_apply hc post' eposts') ⟨pt, hpt, rfl⟩)
    · constructor
      · intro h pt hpt post eposts
        exact PartialOrder.rel_trans (le_csup (chain_apply hc post eposts) ⟨pt, hpt, rfl⟩)
          (h post eposts)
      · intro h post eposts
        refine csup_le (chain_apply hc post eposts) fun p ⟨pt, hpt, hp⟩ => ?_
        subst hp
        exact h pt hpt post eposts

/-- Monotonicity of `pt` as a proposition. Every predicate transformer satisfies it by
`apply_mono`. -/
@[deprecated "every `PredTrans` is monotone by its field `PredTrans.apply_mono`"
  (since := "2026-11-16")]
def Monotone (pt : PredTrans Pred EPosts α) :=
  ∀ post post' eposts eposts', eposts ⊑ eposts' → post ⊑ post' → pt.apply post eposts ⊑ pt.apply post' eposts'

/-- Conjunctivity property for a predicate transformer: the meet of two preconditions lies below
the precondition of the componentwise meet of the postconditions. -/
def Conjunctive {Pred : Type u} {EPosts : Type v} [CompleteLattice Pred] [CompleteLattice EPosts]
    (pt : PredTrans Pred EPosts α) :=
  ∀ post₁ post₂ eposts₁ eposts₂,
    pt.apply post₁ eposts₁ ⊓ pt.apply post₂ eposts₂ ⊑ pt.apply (post₁ ⊓ post₂) (eposts₁ ⊓ eposts₂)

/-!
## Monad Structure
-/

/-- `pure a` applies the postcondition to `a`. -/
def pure (a : α) : PredTrans Pred EPosts α :=
  mk (fun post _epost => post a)
    (fun hpost _ => hpost a)

/-- `bind x f` threads the postcondition through the continuation `f`. -/
def bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β) :
    PredTrans Pred EPosts β :=
  mk (fun post eposts => x.apply (fun a => (f a).apply post eposts) eposts)
    (fun hpost heposts => x.apply_mono (fun a => (f a).apply_mono hpost heposts) heposts)

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
## `apply_*` computation rules

Equations that reduce `(expr).apply post eposts` for each monadic combinator.
-/

/-- Unfolding `PredTrans.pure` through `apply`. -/
theorem apply_pure (a : α) (post : α → Pred) (eposts : EPosts) :
    (PredTrans.pure a : PredTrans Pred EPosts α).apply post eposts = post a := (rfl)

/-- Unfolding `pure` through `apply`. -/
theorem apply_Pure_pure (a : α) (post : α → Pred) (eposts : EPosts) :
    (Pure.pure a : PredTrans Pred EPosts α).apply post eposts = post a := (rfl)

/-- Unfolding `PredTrans.bind` through `apply`. -/
theorem apply_bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β)
    (post : β → Pred) (eposts : EPosts) :
    (x.bind f).apply post eposts = x.apply (fun a => (f a).apply post eposts) eposts := (rfl)

/-- Unfolding `>>=` through `apply`. -/
theorem apply_Bind_bind (x : PredTrans Pred EPosts α) (f : α → PredTrans Pred EPosts β)
    (post : β → Pred) (eposts : EPosts) :
    (x >>= f).apply post eposts = x.apply (fun a => (f a).apply post eposts) eposts := (rfl)

/-- Unfolding `<$>` through `apply`. -/
theorem apply_Functor_map (f : α → β) (x : PredTrans Pred EPosts α)
    (post : β → Pred) (eposts : EPosts) :
    (f <$> x).apply post eposts = x.apply (post ∘ f) eposts := (rfl)

/-- Unfolding `<*>` through `apply`. -/
theorem apply_Seq_seq (f : PredTrans Pred EPosts (α → β)) (x : PredTrans Pred EPosts α)
    (post : β → Pred) (eposts : EPosts) :
    (f <*> x).apply post eposts =
      f.apply (fun g => x.apply (fun a => post (g a)) eposts) eposts := (rfl)

/-- Unfolding `dite` through `apply`. -/
theorem apply_dite (c : Prop) [Decidable c]
    (t : c → PredTrans Pred EPosts α) (e : ¬ c → PredTrans Pred EPosts α)
    (post : α → Pred) (eposts : EPosts) :
    (if h : c then t h else e h).apply post eposts =
      if h : c then (t h).apply post eposts else (e h).apply post eposts := by
  split <;> rfl

/-- Unfolding `ite` through `apply`. -/
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
  mk (fun post eposts s => (x s).apply (fun (a, s) => post a s) eposts)
    (fun hpost heposts s => (x s).apply_mono (fun p => hpost p.1 p.2) heposts)

/-- Unfolding lemma for `pushArg`: applies the state-threaded transformer at state `s`. -/
theorem apply_pushArg {σ : Type z} (x : σ → PredTrans Pred EPosts (α × σ))
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (pushArg x).apply post eposts s = (x s).apply (fun (a, s) => post a s) eposts := (rfl)

/-- Removes the state argument of a predicate transformer by applying it at state `s`.
The transformed result carries the final state. -/
def popArg {σ : Type z} (x : PredTrans (σ → Pred) EPosts α) (s : σ) :
    PredTrans Pred EPosts (α × σ) :=
  mk (fun post eposts => x.apply (fun a s => post (a, s)) eposts s)
    (fun hpost heposts => x.apply_mono (fun a s => hpost (a, s)) heposts s)

/-- Unfolding `popArg` through `apply`. -/
theorem apply_popArg {σ : Type z} (x : PredTrans (σ → Pred) EPosts α) (s : σ)
    (post : α × σ → Pred) (eposts : EPosts) :
    (x.popArg s).apply post eposts = x.apply (fun a s => post (a, s)) eposts s := (rfl)

/-- Adds a state argument that the predicate transformer ignores. -/
def liftArg {σ : Type z} (x : PredTrans Pred EPosts α) : PredTrans (σ → Pred) EPosts α :=
  mk (fun post eposts s => x.apply (fun a => post a s) eposts)
    (fun hpost heposts s => x.apply_mono (fun a => hpost a s) heposts)

/-- Unfolding `liftArg` through `apply`. -/
theorem apply_liftArg {σ : Type z} (x : PredTrans Pred EPosts α)
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (liftArg x : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = x.apply (fun a => post a s) eposts := (rfl)

instance {σ : Type z} : MonadLift (PredTrans Pred EPosts) (PredTrans (σ → Pred) EPosts) where
  monadLift := liftArg

/-- Unfolding `monadLift` through `apply`. -/
theorem apply_monadLift {σ : Type z} (x : PredTrans Pred EPosts α)
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadLift.monadLift x : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = x.apply (fun a => post a s) eposts := (rfl)

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
theorem pushExcept_ok {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (eposts : ε → Pred) (a : α) :
    pushExcept post eposts (.ok a) = post a := (rfl)

/-- An exceptional result uses the exception postcondition. -/
theorem pushExcept_error {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (eposts : ε → Pred) (e : ε) :
    pushExcept post eposts (.error e) = eposts e := (rfl)

/-- The postcondition for an `Option α` result: `some a` uses `post a`, and `none` uses
`eposts ()`. -/
def pushOption {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) : Option α → Pred
  | .some a => post a
  | .none => eposts ()

/-- A present result uses the normal postcondition. -/
theorem pushOption_some {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) (a : α) :
    pushOption post eposts (.some a) = post a := (rfl)

/-- An absent result uses the absent postcondition. -/
theorem pushOption_none {α : Type u} {Pred : Type w}
    (post : α → Pred) (eposts : Unit → Pred) :
    pushOption post eposts .none = eposts () := (rfl)

namespace PredTrans

variable {Pred : Type u} {EPosts : Type v} [PartialOrder Pred] [PartialOrder EPosts] {α β : Type w}

/-- Adds an exception postcondition layer to a predicate transformer, mirroring `ExceptT`.

Given a transformer over `Except ε α`, produces one over `α` with an additional exception
postcondition for `ε`. The normal and error postconditions are combined via `pushExcept`. -/
def pushExceptT {ε : Type z} (x : PredTrans Pred EPosts (Except ε α)) :
    PredTrans Pred ((ε → Pred) × EPosts) α :=
  mk (fun post eposts => x.apply (pushExcept post eposts.fst) eposts.snd)
    (fun hpost heposts => x.apply_mono (fun | .ok a => hpost a | .error e => heposts.1 e) heposts.2)

/-- Unfolding lemma for `pushExceptT`. -/
theorem apply_pushExceptT {ε : Type z}
    (x : PredTrans Pred EPosts (Except ε α)) (post : α → Pred)
    (eposts : (ε → Pred) × EPosts) :
    (pushExceptT x).apply post eposts
      = x.apply (pushExcept post eposts.fst) eposts.snd := (rfl)

/-- Adds an early-termination layer to a predicate transformer, mirroring `OptionT`.

Given a transformer over `Option α`, produces one over `α` with an additional exception
postcondition for the `none` case. -/
def pushOptionT (x : PredTrans Pred EPosts (Option α)) :
    PredTrans Pred ((Unit → Pred) × EPosts) α :=
  mk (fun post eposts => x.apply (pushOption post eposts.fst) eposts.snd)
    (fun hpost heposts => x.apply_mono (fun | .some a => hpost a | .none => heposts.1 ()) heposts.2)

/-- Unfolding lemma for `pushOptionT`. -/
theorem apply_pushOptionT (x : PredTrans Pred EPosts (Option α)) (post : α → Pred)
    (eposts : (Unit → Pred) × EPosts) :
    (pushOptionT x).apply post eposts
      = x.apply (pushOption post eposts.fst) eposts.snd := (rfl)

/-!
## Exception Instances

`throw` and `tryCatch` on the first exception postcondition, and the combinators that lift the
`MonadExceptOf` instance through further layers.
-/

/-- `throw e` asserts the first exception postcondition at `e`. -/
def throw {ε : Type z} (e : ε) : PredTrans Pred ((ε → Pred) × EPosts) α :=
  mk (fun _post eposts => eposts.fst e)
    (fun _ heposts => heposts.1 e)

/-- `tryCatch x handle` replaces the first exception postcondition of `x` with the precondition
of the handler. -/
def tryCatch {ε : Type z} (x : PredTrans Pred ((ε → Pred) × EPosts) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPosts) α) :
    PredTrans Pred ((ε → Pred) × EPosts) α :=
  mk (fun post eposts => x.apply post ((fun e => (handle e).apply post eposts), eposts.snd))
    (fun hpost heposts =>
     x.apply_mono hpost ⟨fun e => (handle e).apply_mono hpost heposts, heposts.2⟩)

instance {ε : Type z} : MonadExceptOf ε (PredTrans Pred ((ε → Pred) × EPosts)) where
  throw := throw
  tryCatch := tryCatch

/-- Unfolding `throw` through `apply`: the first exception postcondition at the thrown value. -/
theorem apply_throw {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} [PartialOrder Pred] [PartialOrder EPosts]
    (e : ε) (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExceptOf.throw e : PredTrans Pred ((ε → Pred) × EPosts) α).apply post eposts
      = eposts.fst e := (rfl)

/-- Unfolding `tryCatch` through `apply`: the handler replaces the first exception
postcondition. -/
theorem apply_tryCatch {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} [PartialOrder Pred] [PartialOrder EPosts]
    (x : PredTrans Pred ((ε → Pred) × EPosts) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPosts) α)
    (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExceptOf.tryCatch x handle).apply post eposts
      = x.apply post ((fun e => (handle e).apply post eposts), eposts.snd) := (rfl)

theorem apply_MonadExcept_throw {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} [PartialOrder Pred] [PartialOrder EPosts]
    (e : ε) (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExcept.throw e : PredTrans Pred ((ε → Pred) × EPosts) α).apply post eposts
      = eposts.fst e := (rfl)

theorem apply_MonadExcept_tryCatch {ε : Type u} {α : Type u} {Pred : Type u}
    {EPosts : Type w} [PartialOrder Pred] [PartialOrder EPosts]
    (x : PredTrans Pred ((ε → Pred) × EPosts) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPosts) α)
    (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    (MonadExcept.tryCatch x handle).apply post eposts
      = x.apply post ((fun e => (handle e).apply post eposts), eposts.snd) := (rfl)

/-- Adds a first exception postcondition that the predicate transformer ignores. -/
def liftExcept {eh : Type z} [PartialOrder eh] (x : PredTrans Pred EPosts α) :
    PredTrans Pred (eh × EPosts) α :=
  mk (fun post eposts => x.apply post eposts.snd)
    (fun hpost heposts => x.apply_mono hpost heposts.2)

/-- Unfolding `liftExcept` through `apply`. -/
theorem apply_liftExcept {eh : Type z} [PartialOrder eh] (x : PredTrans Pred EPosts α)
    (post : α → Pred) (eposts : eh × EPosts) :
    (liftExcept x : PredTrans Pred (eh × EPosts) α).apply post eposts
      = x.apply post eposts.snd := (rfl)

/-- Removes the first exception postcondition of a predicate transformer by fixing it to `h`. -/
def popExcept {eh : Type z} [PartialOrder eh] (x : PredTrans Pred (eh × EPosts) α) (h : eh) :
    PredTrans Pred EPosts α :=
  mk (fun post eposts => x.apply post (h, eposts))
    (fun hpost heposts => x.apply_mono hpost ⟨PartialOrder.rel_refl, heposts⟩)

/-- Unfolding `popExcept` through `apply`. -/
theorem apply_popExcept {eh : Type z} [PartialOrder eh] (x : PredTrans Pred (eh × EPosts) α)
    (h : eh) (post : α → Pred) (eposts : EPosts) :
    (x.popExcept h).apply post eposts = x.apply post (h, eposts) := (rfl)

/-!
## State Instances

Standard state and reader class instances for `PredTrans`.
-/

/-- `get` transforms the postcondition into its assertion at the current state. -/
def get {σ : Type z} : PredTrans (σ → Pred) EPosts σ :=
  mk (fun post _epost s => post s s)
    (fun hpost _ s => hpost s s)

/-- `set s'` transforms the postcondition into its assertion at the state `s'`. -/
def set {σ : Type z} (s' : σ) : PredTrans (σ → Pred) EPosts PUnit :=
  mk (fun post _epost _s => post ⟨⟩ s')
    (fun hpost _ _ => hpost ⟨⟩ s')

/-- `modifyGet f` transforms the postcondition into its assertion at the result and state
computed by `f`. -/
def modifyGet {σ α : Type z} (f : σ → α × σ) : PredTrans (σ → Pred) EPosts α :=
  mk (fun post _epost s => post (f s).1 (f s).2)
    (fun hpost _ s => hpost (f s).1 (f s).2)

instance {σ : Type z} : MonadStateOf σ (PredTrans (σ → Pred) EPosts) where
  get := get
  set := set
  modifyGet := modifyGet

instance {σ : Type z} : MonadReaderOf σ (PredTrans (σ → Pred) EPosts) where
  read := get

/-- Unfolding `get` through `apply`. -/
theorem apply_get {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.get : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := (rfl)

/-- Unfolding `set` through `apply`. -/
theorem apply_set {σ : Type z}
    (s' : σ) (post : PUnit → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.set s' : PredTrans (σ → Pred) EPosts PUnit).apply post eposts s = post ⟨⟩ s' := (rfl)

/-- Unfolding `modifyGet` through `apply`. -/
theorem apply_modifyGet {σ α : Type z}
    (f : σ → α × σ) (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadStateOf.modifyGet f : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = post (f s).1 (f s).2 := (rfl)

/-- Unfolding `read` through `apply`. -/
theorem apply_read {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadReaderOf.read : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := (rfl)

theorem apply_MonadState_get {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadState.get : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := (rfl)

theorem apply_MonadState_modifyGet {σ α : Type z}
    (f : σ → α × σ) (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadState.modifyGet f : PredTrans (σ → Pred) EPosts α).apply post eposts s
      = post (f s).1 (f s).2 := (rfl)

theorem apply_modify {σ : Type z}
    (f : σ → σ) (post : PUnit → σ → Pred) (eposts : EPosts) (s : σ) :
    (modify f : PredTrans (σ → Pred) EPosts PUnit).apply post eposts s = post ⟨⟩ (f s) := (rfl)

theorem apply_modifyThe {σ : Type z}
    (f : σ → σ) (post : PUnit → σ → Pred) (eposts : EPosts) (s : σ) :
    (modifyThe σ f : PredTrans (σ → Pred) EPosts PUnit).apply post eposts s = post ⟨⟩ (f s) := (rfl)

theorem apply_MonadReader_read {σ : Type z}
    (post : σ → σ → Pred) (eposts : EPosts) (s : σ) :
    (MonadReader.read : PredTrans (σ → Pred) EPosts σ).apply post eposts s = post s s := (rfl)

instance {ε : Type u'} {σ : Type z} [MonadExceptOf ε (PredTrans Pred EPosts)] :
    MonadExceptOf ε (PredTrans (σ → Pred) EPosts) where
  throw e := liftArg (MonadExceptOf.throw (m := PredTrans Pred EPosts) e)
  tryCatch x handle := pushArg fun s =>
    MonadExceptOf.tryCatch (m := PredTrans Pred EPosts) (x.popArg s) fun e => (handle e).popArg s

end PredTrans

end Lean.Order

end -- public section
