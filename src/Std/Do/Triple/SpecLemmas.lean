/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.Basic
public import Std.Do.WP
import Init.Data.Range.Polymorphic

@[expose] public section

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

namespace Std.Range

abbrev toList (r : Std.Range) : List Nat :=
  List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

end Std.Range

namespace List

@[ext]
structure Cursor {α : Type u} (l : List α) : Type u where
  «prefix» : List α
  suffix : List α
  property : «prefix» ++ suffix = l

def Cursor.at (l : List α) (n : Nat) : Cursor l := ⟨l.take n, l.drop n, by simp⟩
abbrev Cursor.begin (l : List α) : Cursor l := .at l 0
abbrev Cursor.end (l : List α) : Cursor l := .at l l.length

def Cursor.current {α} {l : List α} (c : Cursor l) (h : 0 < c.suffix.length := by get_elem_tactic) : α :=
  c.suffix[0]'(by simp [h])

def Cursor.tail (s : Cursor l) (h : 0 < s.suffix.length := by get_elem_tactic) : Cursor l :=
  { «prefix» := s.prefix ++ [s.current]
  , suffix := s.suffix.tail
  , property := by
      have : s.suffix ≠ [] := by simp only [List.ne_nil_iff_length_pos, h]
      simp [current, ←List.head_eq_getElem this, s.property] }

@[simp, grind =] theorem Cursor.prefix_at (l : List α) : (Cursor.at l n).prefix = l.take n := rfl
@[simp, grind =] theorem Cursor.suffix_at (l : List α) : (Cursor.at l n).suffix = l.drop n := rfl
@[simp, grind =] theorem Cursor.current_at (l : List α) (h : n < l.length) :
    (Cursor.at l n).current  (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = l[n] := by
  induction n with simp_all [Cursor.current]
@[simp, grind =] theorem Cursor.tail_at (l : List α) (h : n < l.length) :
    (Cursor.at l n).tail (by simpa using Nat.sub_lt_sub_right (Nat.le_refl n) h) = Cursor.at l (n + 1) := by
  simp [Cursor.tail, Cursor.at, Cursor.current]

@[grind →]
theorem eq_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
    cur = s + step * xs.length := by
  rw [range'_eq_append_iff] at h
  obtain ⟨k, hk, hxs, hcur⟩ := h
  have h := (range'_eq_cons_iff.mp hcur.symm).1.symm
  have hk : k = xs.length := by simp_all [length_range']
  simp only [h, hk, Nat.add_left_cancel_iff]
  apply Nat.mul_comm

@[grind →]
theorem length_of_range'_eq_append_cons (h : range' s n step = xs ++ cur :: ys) :
    n = xs.length + ys.length + 1 := by
  have : n = (range' s n step).length := by simp
  simpa [h] using this

@[grind →]
theorem mem_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) :
    i ∈ range' s n step := by simp [h]

@[grind →]
theorem gt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ xs) :
    j < i := by
  obtain ⟨nxs, _, rfl, htail⟩ := range'_eq_append_iff.mp h
  obtain ⟨rfl, _⟩ := range'_eq_cons_iff.mp htail.symm
  simp only [mem_range'] at hj
  obtain ⟨i, _, rfl⟩ := hj
  apply Nat.add_lt_add_left
  simp [Nat.mul_comm, *]

@[grind →]
theorem lt_of_range'_eq_append_cons (h : range' s n step = xs ++ i :: ys) (hstep : 0 < step) (hj : j ∈ ys) :
    i < j := by
  obtain ⟨k, hk, rfl, htail⟩ := range'_eq_append_iff.mp h
  obtain ⟨rfl, _, _, _⟩ := range'_eq_cons_iff.mp htail.symm
  simp only [mem_range'] at hj
  omega

end List

namespace Std.Do

/-! # `Monad` -/

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

theorem Spec.pure' [Monad m] [WPMonad m ps] {P : Assertion ps} {Q : PostCond α ps}
    (h : P ⊢ₛ Q.1 a) :
    Triple (Pure.pure (f:=m) a) (spred(P)) spred(Q) := Triple.pure a h

@[spec]
theorem Spec.pure [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  Triple (Pure.pure (f:=m) a) (spred(Q.1 a)) spred(Q) := Spec.pure' .rfl

theorem Spec.bind' [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : Triple x (spred(P)) (spred(fun a => wp⟦f a⟧ Q), Q.2)) :
    Triple (x >>= f) (spred(P)) spred(Q) := Triple.bind x f h (fun _ => .rfl)

@[spec]
theorem Spec.bind [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  Triple (x >>= f) (spred(wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2))) spred(Q) := Spec.bind' .rfl

@[spec]
theorem Spec.map [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → β} {Q : PostCond β ps} :
  Triple (f <$> x) (spred(wp⟦x⟧ (fun a => Q.1 (f a), Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.seq [Monad m] [WPMonad m ps] {α β} {x : m (α → β)} {y : m α} {Q : PostCond β ps} :
  Triple (x <*> y) (spred(wp⟦x⟧ (fun f => wp⟦y⟧ (fun a => Q.1 (f a), Q.2), Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

/-! # `MonadLift` -/

@[spec]
theorem Spec.monadLift_StateT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  Triple (MonadLift.monadLift x : StateT σ m α) (spred(fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_ReaderT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  Triple (MonadLift.monadLift x : ReaderT ρ m α) (spred(fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_ExceptT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.except ε ps)) :
  Triple (ps:=.except ε ps)
    (MonadLift.monadLift x : ExceptT ε m α)
    (wp⟦x⟧ (fun a => Q.1 a, Q.2.2))
    Q := by simp [Triple, SPred.entails.refl]

/-! # `MonadLiftT` -/

attribute [spec] liftM instMonadLiftTOfMonadLift instMonadLiftT

/-! # `MonadFunctor` -/

@[spec]
theorem Spec.monadMap_StateT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (Q : PostCond α (.arg σ ps)) :
    Triple (MonadFunctor.monadMap (m:=m) f x) (spred(fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2))) spred(Q) := .rfl

@[spec]
theorem Spec.monadMap_ReaderT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ ps)) :
    Triple (MonadFunctor.monadMap (m:=m) f x) (spred(fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2))) spred(Q) := .rfl

@[spec]
theorem Spec.monadMap_ExceptT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (Q : PostCond α (.except ε ps)) :
  Triple (ps:=.except ε ps)
    (MonadFunctor.monadMap (m:=m) f x)
    (wp⟦f x.run⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2))
    Q := by simp only [Triple, WP.monadMap_ExceptT]; rfl

/-! # `MonadFunctorT` -/

@[spec]
theorem Spec.monadMap_trans [WP o ps] [MonadFunctor n o] [MonadFunctorT m n] :
  Triple (ps:=ps)
    (MonadFunctorT.monadMap f x : o α)
    (wp⟦MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α⟧ Q)
    Q := by simp [Triple]

@[spec]
theorem Spec.monadMap_refl [WP m ps] :
  Triple (MonadFunctorT.monadMap f x : m α) (spred(wp⟦f x : m α⟧ Q)) spred(Q) := by simp [Triple]

/-! # `ReaderT` -/

attribute [spec] ReaderT.run

@[spec]
theorem Spec.read_ReaderT [Monad m] [WPMonad m psm] :
  Triple (MonadReaderOf.read : ReaderT ρ m ρ) (spred(fun r => Q.1 r r)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.withReader_ReaderT [WP m psm] :
  Triple (MonadWithReaderOf.withReader f x : ReaderT ρ m α) (spred(fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r))) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.adapt_ReaderT [WP m ps] (f : ρ → ρ') :
  Triple (ReaderT.adapt f x : ReaderT ρ m α) spred(fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r)) spred(Q) := by simp [Triple]

/-! # `StateT` -/

attribute [spec] StateT.run

@[spec]
theorem Spec.get_StateT [Monad m] [WPMonad m psm] :
  Triple (MonadStateOf.get : StateT σ m σ) (spred(fun s => Q.1 s s)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.set_StateT [Monad m] [WPMonad m psm] :
  Triple (MonadStateOf.set s : StateT σ m PUnit) (spred(fun _ => Q.1 ⟨⟩ s)) spred(Q) := by simp [Triple]

@[spec]
theorem Spec.modifyGet_StateT [Monad m] [WPMonad m ps] :
  Triple (MonadStateOf.modifyGet f : StateT σ m α) (spred(fun s => let t := f s; Q.1 t.1 t.2)) spred(Q) := by
    simp [Triple]

/-! # `ExceptT` -/

@[spec]
theorem Spec.run_ExceptT [WP m ps] (x : ExceptT ε m α) :
  Triple (ps:=ps)
    (x.run : m (Except ε α))
    (wp⟦x⟧ (fun a => Q.1 (.ok a), fun e => Q.1 (.error e), Q.2))
    Q := by simp [Triple]

@[spec]
theorem Spec.throw_ExceptT [Monad m] [WPMonad m ps] :
    Triple (MonadExceptOf.throw e : ExceptT ε m α) (spred(Q.2.1 e)) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.tryCatch_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    Triple (MonadExceptOf.tryCatch x h : ExceptT ε m α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    Triple (OrElse.orElse x h : ExceptT ε m α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.adapt_ExceptT [Monad m] [WPMonad m ps] (f : ε → ε') (Q : PostCond α (.except ε' ps)) :
  Triple (ps := .except ε' ps) (ExceptT.adapt f x : ExceptT ε' m α) (wp⟦x⟧ (Q.1, fun e => Q.2.1 (f e), Q.2.2)) Q := by simp [Triple]

/-! # `Except` -/

@[spec]
theorem Spec.throw_Except [Monad m] [WPMonad m ps] :
  Triple (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_Except (Q : PostCond α (.except ε .pure)) :
    Triple (MonadExceptOf.tryCatch x h : Except ε α) (spred(wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.orElse_Except (Q : PostCond α (.except ε .pure)) :
    Triple (OrElse.orElse x h : Except ε α) (spred(wp⟦x⟧ (Q.1, fun _ => wp⟦h ()⟧ Q, Q.2.2))) spred(Q) := by
  simp [Triple]

/-! # `EStateM` -/

@[spec]
theorem Spec.get_EStateM :
  Triple (MonadStateOf.get : EStateM ε σ σ) (spred(fun s => Q.1 s s)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.set_EStateM :
  Triple (MonadStateOf.set s : EStateM ε σ PUnit) (spred(fun _ => Q.1 () s)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.modifyGet_EStateM :
  Triple (MonadStateOf.modifyGet f : EStateM ε σ α) (spred(fun s => let t := f s; Q.1 t.1 t.2)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_EStateM :
  Triple (MonadExceptOf.throw e : EStateM ε σ α) (spred(Q.2.1 e)) spred(Q) := SPred.entails.rfl

open EStateM.Backtrackable in
@[spec]
theorem Spec.tryCatch_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
  Triple (MonadExceptOf.tryCatch x h : EStateM ε σ α) (spred(fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s)) spred(Q) := by
  simp [Triple]

open EStateM.Backtrackable in
@[spec]
theorem Spec.orElse_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
  Triple (OrElse.orElse x h : EStateM ε σ α) (spred(fun s => wp⟦x⟧ (Q.1, fun _ s' => wp⟦h ()⟧ Q (restore s' (save s)), Q.2.2) s)) spred(Q) := by
  simp [Triple]

@[spec]
theorem Spec.adaptExcept_EStateM (f : ε → ε') (Q : PostCond α (.except ε' (.arg σ .pure))) :
  Triple (ps := .except ε' (.arg σ .pure)) (EStateM.adaptExcept f x : EStateM ε' σ α) (wp⟦x⟧ (Q.1, fun e => Q.2.1 (f e), Q.2.2)) Q := by simp [Triple]

/-! # Lifting `MonadStateOf` -/

attribute [spec] modify modifyThe getThe getModify modifyGetThe
  instMonadStateOfMonadStateOf instMonadStateOfOfMonadLift

/-! # Lifting `MonadReaderOf` -/

attribute [spec] readThe withTheReader
  instMonadReaderOfMonadReaderOf instMonadReaderOfOfMonadLift
  instMonadWithReaderOfMonadWithReaderOf instMonadWithReaderOfOfMonadFunctor

/-! # Lifting `MonadExceptOf` -/

attribute [spec] throwThe tryCatchThe

@[spec]
theorem Spec.throw_MonadExcept [MonadExceptOf ε m] [WP m _]:
  Triple (throw e : m α) (spred(wp⟦MonadExceptOf.throw e : m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_MonadExcept [MonadExceptOf ε m] [WP m ps] (Q : PostCond α ps) :
  Triple (tryCatch x h : m α) (spred(wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_ReaderT  [WP m sh] [Monad m] [MonadExceptOf ε m] :
  Triple (MonadExceptOf.throw e : ReaderT ρ m α) (spred(wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
  Triple (MonadExceptOf.throw e : StateT σ m α) (spred(wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT σ m α⟧ Q)) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.throw_ExceptT_lift [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
  Triple (ps:=.except ε' ps)
    (MonadExceptOf.throw e : ExceptT ε' m α)
    (wp⟦MonadExceptOf.throw (ε:=ε) e : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2))
    Q := by
  simp [Triple]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

@[spec]
theorem Spec.tryCatch_ReaderT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg ρ ps)) :
  Triple (MonadExceptOf.tryCatch x h : ReaderT ρ m α) (spred(fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2))) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
  Triple (MonadExceptOf.tryCatch x h : StateT σ m α) (spred(fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun xs => Q.1 xs.1 xs.2, Q.2))) spred(Q) := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_ExceptT_lift [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.except ε' ps)) :
    Triple
      (ps:=.except ε' ps)
      (MonadExceptOf.tryCatch x h : ExceptT ε' m α)
      (wp⟦MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)⟧ (fun | .ok a => Q.1 a | .error e => Q.2.1 e, Q.2.2))
      Q := by
  simp only [Triple, WP.tryCatch_lift_ExceptT]
  apply (wp _).mono
  simp
  intro x
  split <;> rfl

/-! # Lifting `OrElse` -/

/-! # `ForIn` -/

/--
The type of loop invariants used by the specifications of `for ... in ...` loops.
A loop invariant is a `PostCond` that takes as parameters

* A `List.Cursor xs` representing the iteration state of the loop. It is parameterized by the list
  of elements `xs` that the `for` loop iterates over.
* A state tuple of type `β`, which will be a nesting of `MProd`s representing the elaboration of
  `let mut` variables and early return.

The loop specification lemmas will use this in the following way:
Before entering the loop, the cursor's prefix is empty and the suffix is `xs`.
After leaving the loop, the cursor's prefix is `xs` and the suffix is empty.
During the induction step, the invariant holds for a suffix with head element `x`.
After running the loop body, the invariant then holds after shifting `x` to the prefix.
-/
abbrev Invariant {α : Type u} (xs : List α) (β : Type u) (ps : PostShape) :=
  PostCond (List.Cursor xs × β) ps

/--
Helper definition for specifying loop invariants for loops with early return.

`for ... in ...` loops with early return of type `γ` elaborate to a call like this:
```lean
forIn (β := MProd (Option γ) ...) (b := ⟨none, ...⟩) collection loopBody
```
Note that the first component of the `MProd` state tuple is the optional early return value.
It is `none` as long as there was no early return and `some r` if the loop returned early with `r`.

This function allows to specify different invariants for the loop body depending on whether the loop
terminated early or not. When there was an early return, the loop has effectively finished, which is
encoded by the additional `⌜xs.suffix = []⌝` assertion in the invariant. This assertion is vital for
successfully proving the induction step, as it contradicts with the assumption that
`xs.suffix = x::rest` of the inductive hypothesis at the start of the loop body, meaning that users
won't need to prove anything about the bogus case where the loop has returned early yet takes
another iteration of the loop body.
-/
abbrev Invariant.withEarlyReturn
  (onContinue : List.Cursor xs → β → Assertion ps)
  (onReturn : γ → β → Assertion ps)
  (onExcept : ExceptConds ps := ExceptConds.false) :
    Invariant xs (MProd (Option γ) β) ps :=
  ⟨fun ⟨xs, x, b⟩ => spred(
        (⌜x = none⌝ ∧ onContinue xs b)
      ∨ (∃ r, ⌜x = some r⌝ ∧ ⌜xs.suffix = []⌝ ∧ onReturn r b)),
   onExcept⟩

@[spec]
theorem Spec.forIn'_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple (m:=m)
        (f cur (by simp [h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
                 | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
                 | .done b' => inv.1 (⟨xs, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  suffices h : ∀ c,
      Triple
        (forIn' (m:=m) c.suffix init (fun a ha => f a (by simp [←c.property, ha])))
        (inv.1 (c, init))
        (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2)
    from h ⟨[], xs, rfl⟩
  rintro ⟨pref, suff, h⟩
  induction suff generalizing pref init
  case nil => apply Triple.pure; simp [←h]
  case cons x suff ih =>
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => exact step _ _ _ h.symm init
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp
      next b =>
        simp
        have := @ih b (pref ++ [x]) (by simp [h])
        simp at this
        exact this

-- using the postcondition as a constant invariant:
theorem Spec.forIn'_list_const_inv {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ x (hx : x ∈ xs) b,
      Triple
        (f x hx b)
        (inv.1 b)
        (fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)) :
    Triple (forIn' xs init f) (inv.1 init) inv :=
  Spec.forIn'_list (fun p => inv.1 p.2, inv.2) (fun _p c _s h b => step c (by simp [h]) b)

@[spec]
theorem Spec.forIn_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list inv step

-- using the postcondition as a constant invariant:
theorem Spec.forIn_list_const_inv {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ hd b,
      Triple
        (f hd b)
        (inv.1 b)
        (fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)) :
    Triple (forIn xs init f) (inv.1 init) inv :=
  Spec.forIn_list (fun p => inv.1 p.2, inv.2) (fun _p c _s _h b => step c b)

@[spec]
theorem Spec.foldlM_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : β → α → m β}
    (inv : Invariant xs β ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (List.foldlM f init xs) (inv.1 (⟨[], xs, rfl⟩, init)) (fun b => inv.1 (⟨xs, [], by simp⟩, b), inv.2) := by
  have : xs.foldlM f init = forIn xs init (fun a b => .yield <$> f b a) := by
    simp only [List.forIn_yield_eq_foldlM, id_map']
  rw[this]
  apply Spec.forIn_list inv
  simp only [Triple, WPMonad.wp_map, PredTrans.map_apply]
  exact step

-- using the postcondition as a constant invariant:
theorem Spec.foldlM_list_const_inv {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : β → α → m β}
    {inv : PostCond β ps}
    (step : ∀ hd b,
      Triple
        (f b hd)
        (inv.1 b)
        (fun b' => inv.1 b', inv.2)) :
    Triple (List.foldlM f init xs) (inv.1 init) inv :=
    Spec.foldlM_list (fun p => inv.1 p.2, inv.2) (fun _p c _s _h b => step c b)

@[spec]
theorem Spec.forIn'_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [Std.Range.mem_of_mem_range', h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Std.Range.forIn'_eq_forIn'_range', Std.Range.size, Std.Range.size.eq_1]
  apply Spec.forIn'_list inv (fun c hcur b => step c hcur b)

@[spec]
theorem Spec.forIn_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Std.Range.forIn_eq_forIn_range', Std.Range.size]
  apply Spec.forIn_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn'_prange {α β : Type u}
    [Monad m] [WPMonad m ps]
    [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {xs : PRange ⟨sl, su⟩ α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [←mem_toList_iff_mem, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn'_eq_forIn'_toList]
  apply Spec.forIn'_list inv step

open Std.PRange in
@[spec]
theorem Spec.forIn_prange {α β : Type u}
    [Monad m] [WPMonad m ps]
    [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {xs : PRange ⟨sl, su⟩ α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [forIn]
  apply Spec.forIn'_prange inv step

@[spec]
theorem Spec.forIn'_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur (by simp [←Array.mem_toList_iff, h]) b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn' xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.forIn'_list inv step

@[spec]
theorem Spec.forIn_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.forIn_list inv step

@[spec]
theorem Spec.foldlM_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : β → α → m β}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h : xs.toList = pref ++ cur :: suff) b,
      Triple
        (f b cur)
        (inv.1 (⟨pref, cur::suff, h.symm⟩, b))
        (fun b' => inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, b'), inv.2)) :
    Triple (Array.foldlM f init xs) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  cases xs
  simp
  apply Spec.foldlM_list inv step
