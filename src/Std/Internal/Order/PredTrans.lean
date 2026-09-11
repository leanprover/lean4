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

`PredTrans Pred EPred α` wraps a map from a normal postcondition `α → Pred` and an exception
postcondition `EPred` to a precondition `Pred`. The order and the chain-complete suprema are the
pointwise ones of the function space.

`PredTrans Pred EPred` is a monad, so monadic programs can be interpreted by a monad morphism into
it. This module provides that monad structure, the `apply` simp framework of the monadic
combinators, the `push` family that moves a result type into a postcondition, and the standard
monad class instances.
-/

namespace Lean.Order

/-- A predicate transformer from postconditions to preconditions.

Given a return type `α`, a lattice `Pred` for assertions, and an exception assertion type `EPred`,
`PredTrans Pred EPred α` wraps a function `(α → Pred) → EPred → Pred`. -/
structure PredTrans (Pred : Type u) (EPred : Type v) (α : Type w) where
  /-- Apply the predicate transformer to a postcondition and exception postcondition. -/
  apply : (α → Pred) → EPred → Pred

namespace PredTrans

variable {Pred : Type u} {EPred : Type v} {α β : Type w}

/-- Extensionality for predicate transformers. -/
@[ext] theorem ext {x y : PredTrans Pred EPred α}
    (h : ∀ post epost, x.apply post epost = y.apply post epost) : x = y := by
  cases x; cases y; congr; funext post epost; exact h post epost

/-- Partial order on predicate transformers, inherited from the function space. -/
instance [PartialOrder Pred] : PartialOrder (PredTrans Pred EPred α) where
  rel x y := x.apply ⊑ y.apply
  rel_refl := PartialOrder.rel_refl
  rel_trans h1 h2 := PartialOrder.rel_trans h1 h2
  rel_antisymm h1 h2 := ext fun post epost =>
    PartialOrder.rel_antisymm (h1 post epost) (h2 post epost)

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. -/
instance [CCPO Pred] : CCPO (PredTrans Pred EPred α) where
  has_csup {c} hc := by
    let c' : ((α → Pred) → EPred → Pred) → Prop := fun f => ∃ pt, c pt ∧ pt.apply = f
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

/-- Monotonicity property for a predicate transformer: if both `post` and `epost` grow,
then the resulting precondition grows. -/
def monotone [PartialOrder Pred] [PartialOrder EPred] (pt : PredTrans Pred EPred α) :=
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt.apply post epost ⊑ pt.apply post' epost'

/-!
## Monad Structure
-/

/-- `pure a` applies the postcondition to `a`. -/
def pure (a : α) : PredTrans Pred EPred α :=
  ⟨fun post _epost => post a⟩

/-- `bind x f` threads the postcondition through the continuation `f`. -/
def bind (x : PredTrans Pred EPred α) (f : α → PredTrans Pred EPred β) :
    PredTrans Pred EPred β :=
  ⟨fun post epost => x.apply (fun a => (f a).apply post epost) epost⟩

instance instMonad : Monad (PredTrans Pred EPred) where
  pure := pure
  bind := bind

instance instLawfulMonad : LawfulMonad (PredTrans Pred EPred) where
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

Simp lemmas for reducing `(expr).apply post epost` for each monadic combinator.
-/

/-- Unfolding `PredTrans.pure` through `apply`. -/
@[simp, grind =]
theorem apply_pure (a : α) (post : α → Pred) (epost : EPred) :
    (PredTrans.pure a : PredTrans Pred EPred α).apply post epost = post a := rfl

/-- Unfolding `pure` through `apply`. -/
@[simp, grind =]
theorem apply_Pure_pure (a : α) (post : α → Pred) (epost : EPred) :
    (Pure.pure a : PredTrans Pred EPred α).apply post epost = post a := rfl

/-- Unfolding `PredTrans.bind` through `apply`. -/
@[simp, grind =]
theorem apply_bind (x : PredTrans Pred EPred α) (f : α → PredTrans Pred EPred β)
    (post : β → Pred) (epost : EPred) :
    (x.bind f).apply post epost = x.apply (fun a => (f a).apply post epost) epost := rfl

/-- Unfolding `>>=` through `apply`. -/
@[simp, grind =]
theorem apply_Bind_bind (x : PredTrans Pred EPred α) (f : α → PredTrans Pred EPred β)
    (post : β → Pred) (epost : EPred) :
    (x >>= f).apply post epost = x.apply (fun a => (f a).apply post epost) epost := rfl

/-- Unfolding `<$>` through `apply`. -/
@[simp, grind =]
theorem apply_Functor_map (f : α → β) (x : PredTrans Pred EPred α)
    (post : β → Pred) (epost : EPred) :
    (f <$> x).apply post epost = x.apply (post ∘ f) epost := rfl

/-- Unfolding `<*>` through `apply`. -/
@[simp]
theorem apply_Seq_seq (f : PredTrans Pred EPred (α → β)) (x : PredTrans Pred EPred α)
    (post : β → Pred) (epost : EPred) :
    (f <*> x).apply post epost =
      f.apply (fun g => x.apply (fun a => post (g a)) epost) epost := rfl

/-- Unfolding `dite` through `apply`. -/
@[simp]
theorem apply_dite (c : Prop) [Decidable c]
    (t : c → PredTrans Pred EPred α) (e : ¬ c → PredTrans Pred EPred α)
    (post : α → Pred) (epost : EPred) :
    (if h : c then t h else e h).apply post epost =
      if h : c then (t h).apply post epost else (e h).apply post epost := by
  split <;> rfl

/-- Unfolding `ite` through `apply`. -/
@[simp]
theorem apply_ite (c : Prop) [Decidable c]
    (t : PredTrans Pred EPred α) (e : PredTrans Pred EPred α)
    (post : α → Pred) (epost : EPred) :
    (if c then t else e).apply post epost =
      if c then t.apply post epost else e.apply post epost := by
  split <;> rfl

/-!
## Arguments

Combinators that add or remove a state argument.
-/

/-- Adds a state argument to a predicate transformer.

Given a state-dependent transformer `σ → PredTrans Pred EPred (α × σ)`, produces a transformer
over `σ → Pred` that threads the state through postconditions. -/
def pushArg {σ : Type z} (x : σ → PredTrans Pred EPred (α × σ)) :
    PredTrans (σ → Pred) EPred α :=
  ⟨fun post epost s => (x s).apply (fun (a, s) => post a s) epost⟩

/-- Unfolding lemma for `pushArg`: applies the state-threaded transformer at state `s`. -/
@[simp, grind =]
theorem apply_pushArg {σ : Type z} (x : σ → PredTrans Pred EPred (α × σ))
    (post : α → σ → Pred) (epost : EPred) (s : σ) :
    (pushArg x).apply post epost s = (x s).apply (fun (a, s) => post a s) epost := rfl

/-- Removes the state argument of a predicate transformer by applying it at state `s`.
The transformed result carries the final state. -/
def popArg {σ : Type z} (x : PredTrans (σ → Pred) EPred α) (s : σ) :
    PredTrans Pred EPred (α × σ) :=
  ⟨fun post epost => x.apply (fun a s => post (a, s)) epost s⟩

/-- Unfolding `popArg` through `apply`. -/
@[simp, grind =]
theorem apply_popArg {σ : Type z} (x : PredTrans (σ → Pred) EPred α) (s : σ)
    (post : α × σ → Pred) (epost : EPred) :
    (x.popArg s).apply post epost = x.apply (fun a s => post (a, s)) epost s := rfl

/-- Adds a state argument that the predicate transformer ignores. -/
def liftArg {σ : Type z} (x : PredTrans Pred EPred α) : PredTrans (σ → Pred) EPred α :=
  ⟨fun post epost s => x.apply (fun a => post a s) epost⟩

/-- Unfolding `liftArg` through `apply`. -/
@[simp, grind =]
theorem apply_liftArg {σ : Type z} (x : PredTrans Pred EPred α)
    (post : α → σ → Pred) (epost : EPred) (s : σ) :
    (liftArg x : PredTrans (σ → Pred) EPred α).apply post epost s
      = x.apply (fun a => post a s) epost := rfl

instance {σ : Type z} : MonadLift (PredTrans Pred EPred) (PredTrans (σ → Pred) EPred) where
  monadLift := liftArg

/-- Unfolding `monadLift` through `apply`. -/
@[simp, grind =]
theorem apply_monadLift {σ : Type z} (x : PredTrans Pred EPred α)
    (post : α → σ → Pred) (epost : EPred) (s : σ) :
    (MonadLift.monadLift x : PredTrans (σ → Pred) EPred α).apply post epost s
      = x.apply (fun a => post a s) epost := rfl

end PredTrans

/-!
## Results

Postconditions for `Except` and `Option` results, and the transformer combinators built on them.
-/

/-- The postcondition for an `Except ε α` result: `ok a` uses `post a`, and `error e` uses
`epost e`. -/
def pushExcept {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (epost : ε → Pred) : Except ε α → Pred
  | .ok a => post a
  | .error e => epost e

/-- A normal result uses the normal postcondition. -/
@[simp, grind =] theorem pushExcept_ok {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (epost : ε → Pred) (a : α) :
    pushExcept post epost (.ok a) = post a := rfl

/-- An exceptional result uses the exception postcondition. -/
@[simp, grind =] theorem pushExcept_error {α : Type u} {ε : Type v} {Pred : Type w}
    (post : α → Pred) (epost : ε → Pred) (e : ε) :
    pushExcept post epost (.error e) = epost e := rfl

/-- The postcondition for an `Option α` result: `some a` uses `post a`, and `none` uses
`epost ()`. -/
def pushOption {α : Type u} {Pred : Type w}
    (post : α → Pred) (epost : Unit → Pred) : Option α → Pred
  | .some a => post a
  | .none => epost ()

/-- A present result uses the normal postcondition. -/
@[simp, grind =] theorem pushOption_some {α : Type u} {Pred : Type w}
    (post : α → Pred) (epost : Unit → Pred) (a : α) :
    pushOption post epost (.some a) = post a := rfl

/-- An absent result uses the absent postcondition. -/
@[simp, grind =] theorem pushOption_none {α : Type u} {Pred : Type w}
    (post : α → Pred) (epost : Unit → Pred) :
    pushOption post epost .none = epost () := rfl

namespace PredTrans

variable {Pred : Type u} {EPred : Type v} {α β : Type w}

/-- Adds an exception postcondition layer to a predicate transformer, mirroring `ExceptT`.

Given a transformer over `Except ε α`, produces one over `α` with an additional exception
postcondition for `ε`. The normal and error postconditions are combined via `pushExcept`. -/
def pushExceptT {ε : Type z} (x : PredTrans Pred EPred (Except ε α)) :
    PredTrans Pred ((ε → Pred) × EPred) α :=
  ⟨fun post epost => x.apply (pushExcept post epost.fst) epost.snd⟩

/-- Unfolding lemma for `pushExceptT`. -/
@[simp, grind =]
theorem apply_pushExceptT {ε : Type z}
    (x : PredTrans Pred EPred (Except ε α)) (post : α → Pred)
    (epost : (ε → Pred) × EPred) :
    (pushExceptT x).apply post epost
      = x.apply (pushExcept post epost.fst) epost.snd := rfl

/-- Adds an early-termination layer to a predicate transformer, mirroring `OptionT`.

Given a transformer over `Option α`, produces one over `α` with an additional exception
postcondition for the `none` case. -/
def pushOptionT (x : PredTrans Pred EPred (Option α)) :
    PredTrans Pred ((Unit → Pred) × EPred) α :=
  ⟨fun post epost => x.apply (pushOption post epost.fst) epost.snd⟩

/-- Unfolding lemma for `pushOptionT`. -/
@[simp, grind =]
theorem apply_pushOptionT (x : PredTrans Pred EPred (Option α)) (post : α → Pred)
    (epost : (Unit → Pred) × EPred) :
    (pushOptionT x).apply post epost
      = x.apply (pushOption post epost.fst) epost.snd := rfl

/-!
## Exception Instances

`throw` and `tryCatch` on the first exception postcondition, and the combinators that lift the
`MonadExceptOf` instance through further layers.
-/

/-- `throw e` asserts the first exception postcondition at `e`. -/
def throw {ε : Type z} (e : ε) : PredTrans Pred ((ε → Pred) × EPred) α :=
  ⟨fun _post epost => epost.fst e⟩

/-- `tryCatch x handle` replaces the first exception postcondition of `x` with the precondition
of the handler. -/
def tryCatch {ε : Type z} (x : PredTrans Pred ((ε → Pred) × EPred) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPred) α) :
    PredTrans Pred ((ε → Pred) × EPred) α :=
  ⟨fun post epost => x.apply post ((fun e => (handle e).apply post epost), epost.snd)⟩

instance {ε : Type z} : MonadExceptOf ε (PredTrans Pred ((ε → Pred) × EPred)) where
  throw := throw
  tryCatch := tryCatch

/-- Unfolding `throw` through `apply`: the first exception postcondition at the thrown value. -/
@[simp, grind =] theorem apply_throw {ε : Type u} {α : Type u} {Pred : Type u}
    {EPred : Type w} (e : ε) (post : α → Pred) (epost : (ε → Pred) × EPred) :
    (MonadExceptOf.throw e : PredTrans Pred ((ε → Pred) × EPred) α).apply post epost
      = epost.fst e := rfl

/-- Unfolding `tryCatch` through `apply`: the handler replaces the first exception
postcondition. -/
@[simp, grind =] theorem apply_tryCatch {ε : Type u} {α : Type u} {Pred : Type u}
    {EPred : Type w} (x : PredTrans Pred ((ε → Pred) × EPred) α)
    (handle : ε → PredTrans Pred ((ε → Pred) × EPred) α)
    (post : α → Pred) (epost : (ε → Pred) × EPred) :
    (MonadExceptOf.tryCatch x handle).apply post epost
      = x.apply post ((fun e => (handle e).apply post epost), epost.snd) := rfl

/-- Adds a first exception postcondition that the predicate transformer ignores. -/
def liftExcept {eh : Type z} (x : PredTrans Pred EPred α) : PredTrans Pred (eh × EPred) α :=
  ⟨fun post epost => x.apply post epost.snd⟩

/-- Unfolding `liftExcept` through `apply`. -/
@[simp, grind =]
theorem apply_liftExcept {eh : Type z} (x : PredTrans Pred EPred α) (post : α → Pred)
    (epost : eh × EPred) :
    (liftExcept x : PredTrans Pred (eh × EPred) α).apply post epost
      = x.apply post epost.snd := rfl

/-- Removes the first exception postcondition of a predicate transformer by fixing it to `h`. -/
def popExcept {eh : Type z} (x : PredTrans Pred (eh × EPred) α) (h : eh) :
    PredTrans Pred EPred α :=
  ⟨fun post epost => x.apply post (h, epost)⟩

/-- Unfolding `popExcept` through `apply`. -/
@[simp, grind =]
theorem apply_popExcept {eh : Type z} (x : PredTrans Pred (eh × EPred) α) (h : eh)
    (post : α → Pred) (epost : EPred) :
    (x.popExcept h).apply post epost = x.apply post (h, epost) := rfl

instance {ε : Type u} {Pred : Type v} {EPred : Type w} {ε' : Type u}
    [MonadExceptOf ε (PredTrans Pred EPred)] :
    MonadExceptOf ε (PredTrans Pred ((ε' → Pred) × EPred)) where
  throw e := liftExcept (MonadExceptOf.throw (m := PredTrans Pred EPred) e)
  tryCatch x handle := ⟨fun post epost =>
    (MonadExceptOf.tryCatch (m := PredTrans Pred EPred) (x.popExcept epost.fst)
      fun e => (handle e).popExcept epost.fst).apply post epost.snd⟩

/-!
## State Instances

Standard state and reader class instances for `PredTrans`.
-/

/-- `get` transforms the postcondition into its assertion at the current state. -/
def get {σ : Type z} : PredTrans (σ → Pred) EPred σ :=
  ⟨fun post _epost s => post s s⟩

/-- `set s'` transforms the postcondition into its assertion at the state `s'`. -/
def set {σ : Type z} (s' : σ) : PredTrans (σ → Pred) EPred PUnit :=
  ⟨fun post _epost _s => post ⟨⟩ s'⟩

/-- `modifyGet f` transforms the postcondition into its assertion at the result and state
computed by `f`. -/
def modifyGet {σ α : Type z} (f : σ → α × σ) : PredTrans (σ → Pred) EPred α :=
  ⟨fun post _epost s => post (f s).1 (f s).2⟩

instance {σ : Type z} : MonadStateOf σ (PredTrans (σ → Pred) EPred) where
  get := get
  set := set
  modifyGet := modifyGet

instance {σ : Type z} : MonadReaderOf σ (PredTrans (σ → Pred) EPred) where
  read := get

/-- Unfolding `get` through `apply`. -/
@[simp, grind =] theorem apply_get {σ : Type z}
    (post : σ → σ → Pred) (epost : EPred) (s : σ) :
    (MonadStateOf.get : PredTrans (σ → Pred) EPred σ).apply post epost s = post s s := rfl

/-- Unfolding `set` through `apply`. -/
@[simp, grind =] theorem apply_set {σ : Type z}
    (s' : σ) (post : PUnit → σ → Pred) (epost : EPred) (s : σ) :
    (MonadStateOf.set s' : PredTrans (σ → Pred) EPred PUnit).apply post epost s = post ⟨⟩ s' := rfl

/-- Unfolding `modifyGet` through `apply`. -/
@[simp, grind =] theorem apply_modifyGet {σ α : Type z}
    (f : σ → α × σ) (post : α → σ → Pred) (epost : EPred) (s : σ) :
    (MonadStateOf.modifyGet f : PredTrans (σ → Pred) EPred α).apply post epost s
      = post (f s).1 (f s).2 := rfl

/-- Unfolding `read` through `apply`. -/
@[simp, grind =] theorem apply_read {σ : Type z}
    (post : σ → σ → Pred) (epost : EPred) (s : σ) :
    (MonadReaderOf.read : PredTrans (σ → Pred) EPred σ).apply post epost s = post s s := rfl

instance {ε : Type u'} {σ : Type z} [MonadExceptOf ε (PredTrans Pred EPred)] :
    MonadExceptOf ε (PredTrans (σ → Pred) EPred) where
  throw e := liftArg (MonadExceptOf.throw (m := PredTrans Pred EPred) e)
  tryCatch x handle := pushArg fun s =>
    MonadExceptOf.tryCatch (m := PredTrans Pred EPred) (x.popArg s) fun e => (handle e).popArg s

end PredTrans

end Lean.Order

end -- public section
