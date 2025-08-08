/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.Basic
public import Std.Do.WP

@[expose] public section

/-!
# Hoare triple specifications for select functions

This module contains Hoare triple specifications for some functions in Core.
-/

namespace Std.Range

abbrev toList (r : Std.Range) : List Nat :=
  List.range' r.start ((r.stop - r.start + r.step - 1) / r.step) r.step

theorem mem_of_mem_toList {r : Std.Range} (h : x ∈ r.toList) : x ∈ r := by
  simp only [toList] at h
  apply Std.Range.mem_of_mem_range' h

end Std.Range

namespace Std.Do

-- We override the `Triple` notation in `Std.Do.Triple.Basic` just in this module.
-- The reason is that the actual `Triple` notation is implemented as an elaborator in
-- `Lean.Elab.Tactic.Do.Syntax` for reasons such as #8766. Perhaps #8074 will help.
@[inherit_doc Std.Do.Triple]
local notation:lead (priority := high) "⦃" P "} " x:lead " ⦃" Q "}" => Triple x (spred(P)) spred(Q)

/-! # `Monad` -/

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

theorem Spec.pure' [Monad m] [WPMonad m ps] {P : Assertion ps} {Q : PostCond α ps}
    (h : P ⊢ₛ Q.1 a) :
    ⦃P} Pure.pure (f:=m) a ⦃Q} := Triple.pure a h

@[spec]
theorem Spec.pure [Monad m] [WPMonad m ps] {α} {a : α} {Q : PostCond α ps} :
  ⦃Q.1 a} Pure.pure (f:=m) a ⦃Q} := Spec.pure' .rfl

theorem Spec.bind' [Monad m] [WPMonad m ps] {x : m α} {f : α → m β} {P : Assertion ps} {Q : PostCond β ps}
    (h : ⦃P} x ⦃(fun a => wp⟦f a⟧ Q, Q.2)}) :
    ⦃P} (x >>= f) ⦃Q} := Triple.bind x f h (fun _ => .rfl)

@[spec]
theorem Spec.bind [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → m β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2)} (x >>= f) ⦃Q} := Spec.bind' .rfl

@[spec]
theorem Spec.map [Monad m] [WPMonad m ps] {α β} {x : m α} {f : α → β} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun a => Q.1 (f a), Q.2)} (f <$> x) ⦃Q} := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.seq [Monad m] [WPMonad m ps] {α β} {x : m (α → β)} {y : m α} {Q : PostCond β ps} :
  ⦃wp⟦x⟧ (fun f => wp⟦y⟧ (fun a => Q.1 (f a), Q.2), Q.2)} (x <*> y) ⦃Q} := by simp [Triple, SPred.entails.refl]

/-! # `MonadLift` -/

@[spec]
theorem Spec.monadLift_StateT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg σ ps)) :
  ⦃fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2)} (MonadLift.monadLift x : StateT σ m α) ⦃Q} := by simp [Triple, SPred.entails.refl]

@[spec]
theorem Spec.monadLift_ReaderT [Monad m] [WPMonad m ps] (x : m α) (Q : PostCond α (.arg ρ ps)) :
  ⦃fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2)} (MonadLift.monadLift x : ReaderT ρ m α) ⦃Q} := by simp [Triple, SPred.entails.refl]

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
    ⦃fun s => wp⟦f (x.run s)⟧ (fun (a, s) => Q.1 a s, Q.2)} (MonadFunctor.monadMap (m:=m) f x) ⦃Q} := .rfl

@[spec]
theorem Spec.monadMap_ReaderT [Monad m] [WP m ps]
    (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (Q : PostCond α (.arg ρ ps)) :
    ⦃fun s => wp⟦f (x.run s)⟧ (fun a => Q.1 a s, Q.2)} (MonadFunctor.monadMap (m:=m) f x) ⦃Q} := .rfl

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
  ⦃wp⟦f x : m α⟧ Q}
  (MonadFunctorT.monadMap f x : m α)
  ⦃Q} := by simp [Triple]

/-! # `ReaderT` -/

attribute [spec] ReaderT.run

@[spec]
theorem Spec.read_ReaderT [Monad m] [WPMonad m psm] :
  ⦃fun r => Q.1 r r} (MonadReaderOf.read : ReaderT ρ m ρ) ⦃Q} := by simp [Triple]

@[spec]
theorem Spec.withReader_ReaderT [Monad m] [WPMonad m psm] :
  ⦃fun r => wp⟦x⟧ (fun a _ => Q.1 a r, Q.2) (f r)} (MonadWithReaderOf.withReader f x : ReaderT ρ m α) ⦃Q} := by simp [Triple]

/-! # `StateT` -/

attribute [spec] StateT.run

@[spec]
theorem Spec.get_StateT [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s} (MonadStateOf.get : StateT σ m σ) ⦃Q} := by simp [Triple]

@[spec]
theorem Spec.set_StateT [Monad m] [WPMonad m psm] :
  ⦃fun _ => Q.1 ⟨⟩ s} (MonadStateOf.set s : StateT σ m PUnit) ⦃Q} := by simp [Triple]

@[spec]
theorem Spec.modifyGet_StateT [Monad m] [WPMonad m ps] :
  ⦃fun s => let t := f s; Q.1 t.1 t.2} (MonadStateOf.modifyGet f : StateT σ m α) ⦃Q} := by
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
    ⦃Q.2.1 e} (MonadExceptOf.throw e : ExceptT ε m α) ⦃Q} := by
  simp [Triple]

@[spec]
theorem Spec.tryCatch_ExceptT [Monad m] [WPMonad m ps] (Q : PostCond α (.except ε ps)) :
    ⦃wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2)} (MonadExceptOf.tryCatch x h : ExceptT ε m α) ⦃Q} := by
  simp [Triple]

/-! # `Except` -/

@[spec]
theorem Spec.throw_Except [Monad m] [WPMonad m ps] :
    ⦃Q.2.1 e} (MonadExceptOf.throw e : Except ε α) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_Except (Q : PostCond α (.except ε .pure)) :
    ⦃wp⟦x⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.2.2)} (MonadExceptOf.tryCatch x h : Except ε α) ⦃Q} := by
  simp [Triple]

/-! # `EStateM` -/

@[spec]
theorem Spec.get_EStateM :
  ⦃fun s => Q.1 s s} (MonadStateOf.get : EStateM ε σ σ) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.set_EStateM :
  ⦃fun _ => Q.1 () s} (MonadStateOf.set s : EStateM ε σ PUnit) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.modifyGet_EStateM :
    ⦃fun s => let t := f s; Q.1 t.1 t.2} (MonadStateOf.modifyGet f : EStateM ε σ α) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.throw_EStateM :
    ⦃Q.2.1 e} (MonadExceptOf.throw e : EStateM ε σ α) ⦃Q} := SPred.entails.rfl

open EStateM.Backtrackable in
@[spec]
theorem Spec.tryCatch_EStateM (Q : PostCond α (.except ε (.arg σ .pure))) :
    ⦃fun s => wp⟦x⟧ (Q.1, fun e s' => wp⟦h e⟧ Q (restore s' (save s)), Q.2.2) s} (MonadExceptOf.tryCatch x h : EStateM ε σ α) ⦃Q} := by
  simp [Triple]

/-! # Lifting `MonadStateOf` -/

attribute [spec] modify modifyThe getThe
  instMonadStateOfMonadStateOf instMonadStateOfOfMonadLift

/-! # Lifting `MonadReaderOf` -/

attribute [spec] readThe withTheReader
  instMonadReaderOfMonadReaderOf instMonadReaderOfOfMonadLift
  instMonadWithReaderOfMonadWithReaderOf instMonadWithReaderOfOfMonadFunctor

/-! # Lifting `MonadExceptOf` -/

attribute [spec] throwThe tryCatchThe

@[spec]
theorem Spec.throw_MonadExcept [MonadExceptOf ε m] [WP m _]:
    ⦃wp⟦MonadExceptOf.throw e : m α⟧ Q} (throw e : m α) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_MonadExcept [MonadExceptOf ε m] [WP m ps] (Q : PostCond α ps) :
    ⦃wp⟦MonadExceptOf.tryCatch x h : m α⟧ Q} (tryCatch x h : m α) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.throw_ReaderT  [WP m sh] [Monad m] [MonadExceptOf ε m] :
    ⦃wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : ReaderT ρ m α⟧ Q} (MonadExceptOf.throw e : ReaderT ρ m α) ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.throw_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
    ⦃wp⟦MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) e : m α) : StateT σ m α⟧ Q} (MonadExceptOf.throw e : StateT σ m α) ⦃Q} := SPred.entails.rfl

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
    ⦃fun r => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α⟧ (fun a => Q.1 a r, Q.2)}
    (MonadExceptOf.tryCatch x h : ReaderT ρ m α)
    ⦃Q} := SPred.entails.rfl

@[spec]
theorem Spec.tryCatch_StateT [WP m ps] [Monad m] [MonadExceptOf ε m] (Q : PostCond α (.arg σ ps)) :
    ⦃fun s => wp⟦MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)⟧ (fun xs => Q.1 xs.1 xs.2, Q.2)}
    (MonadExceptOf.tryCatch x h : StateT σ m α)
    ⦃Q} := SPred.entails.rfl

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

/-! # `ForIn` -/

@[spec]
theorem Spec.forIn'_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 (b, ⟨xs, i, by omega⟩)}
        f xs[i] (by simp) b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs, Fin.last xs.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs, 0, by omega⟩)} forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs, Fin.last xs.length, by omega⟩), inv.2)} := by
  suffices h : ∀ (i : Fin (xs.length + 1)) xs' (h : xs.drop i = xs'),
      ⦃inv.1 (init, ⟨xs, i, by omega⟩)}
      forIn' (m:=m) xs' init (fun a ha => f a (by cases h.symm; exact List.mem_of_mem_drop ha))
      ⦃(fun b => inv.1 (b, ⟨xs, Fin.last xs.length, by omega⟩), inv.2)}
    from h 0 xs (by simp)
  intro i xs hxs
  induction i using Fin.reverseInduction generalizing xs init
  case last =>
    simp only [hxs.symm, Fin.val_last, List.drop_length, List.forIn'_nil]
    apply Triple.pure
    rfl
  case cast i ih =>
    simp only [Fin.coe_castSucc] at hxs
    rw [← List.getElem_cons_drop_succ_eq_drop i.isLt] at hxs
    subst hxs
    simp only [List.forIn'_cons]
    apply Triple.bind
    case hx => apply step _ _ _ i.isLt rfl
    case hf =>
      intro r
      split
      next => apply Triple.pure; simp
      next b => apply ih; simp

-- using the postcondition as a constant invariant:
theorem Spec.forIn'_list_const_inv {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 b}
        f xs[i] (by simp) b
        ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)}) :
    ⦃inv.1 init} forIn' xs init f ⦃inv} :=
  Spec.forIn'_list (fun p => inv.1 p.1, inv.2) step

@[spec]
theorem Spec.forIn_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 (b, ⟨xs, i, by omega⟩)}
        f xs[i] b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs, Fin.last xs.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs, 0, by omega⟩)} forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs, Fin.last xs.length, by omega⟩), inv.2)} := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_list inv step

-- using the postcondition as a constant invariant:
theorem Spec.forIn_list_const_inv {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
    {inv : PostCond β ps}
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 b}
        f xs[i] b
        ⦃(fun r => match r with | .yield b' => inv.1 b' | .done b' => inv.1 b', inv.2)}) :
    ⦃inv.1 init} forIn xs init f ⦃inv} :=
  Spec.forIn_list (fun p => inv.1 p.1, inv.2) step

@[spec]
theorem Spec.foldlM_list {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : List α} {init : β} {f : β → α → m β}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 (b, ⟨xs, i, by omega⟩)}
        f b xs[i]
        ⦃(fun b' => inv.1 (b', ⟨xs, i + 1, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs, 0, by omega⟩)} List.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs, Fin.last xs.length, by omega⟩), inv.2)} := by
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
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.length),
        ⦃inv.1 b}
        f b xs[i]
        ⦃(fun b' => inv.1 b', inv.2)}) :
  ⦃inv.1 init} List.foldlM f init xs ⦃inv} :=
    Spec.foldlM_list (fun p => inv.1 p.1, inv.2) step

private theorem Spec.forIn'_range_aux {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (n : Nat) (h : n = xs.size)
    (inv : PostCond (β × Σ (xs : List Nat), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (hi : i < len) (hxs : len = n),
        let h : i < xs.toList.length := by simpa [h, hxs] using hi
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f xs.toList[i] (by apply_rules [Std.Range.mem_of_mem_toList, List.getElem_mem]) b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} := by
  simp only [Std.Range.forIn'_eq_forIn'_range']
  have : n = xs.toList.length := by simp [h]
  subst this
  apply Spec.forIn'_list inv step

@[spec]
theorem Spec.forIn'_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : (a : Nat) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List Nat), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.size),
        let h : i < xs.toList.length := by simpa [hxs] using h
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f xs.toList[i] (by apply_rules [Std.Range.mem_of_mem_toList, List.getElem_mem]) b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} :=
  Spec.forIn'_range_aux xs.size rfl inv step

@[spec]
theorem Spec.forIn_range {β : Type} {m : Type → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List Nat), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.size),
        let h : i < xs.toList.length := by simpa [hxs] using h
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f xs.toList[i] b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} := by
  simp only [← forIn'_eq_forIn]
  exact Spec.forIn'_range inv step

@[spec]
theorem Spec.forIn'_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.size),
        let h : i < xs.toList.length := by simpa [hxs] using h
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f xs[i] (by simp) b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} forIn' xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} := by
  cases xs
  simp
  apply Spec.forIn'_list inv fun b i h => by simp only [Fin.val_last]; exact step b i h

@[spec]
theorem Spec.forIn_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : α → β → m (ForInStep β)}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.size),
        let h : i < xs.toList.length := by simpa [hxs] using h
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f xs[i] b
        ⦃(fun r => match r with
                   | .yield b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩)
                   | .done b' => inv.1 (b', ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} forIn xs init f ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} := by
  cases xs
  simp only [List.forIn_toArray]
  apply Spec.forIn_list inv step

@[spec]
theorem Spec.foldlM_array {α β : Type u}
    [Monad m] [WPMonad m ps]
    {xs : Array α} {init : β} {f : β → α → m β}
    (inv : PostCond (β × Σ (xs : List α), Fin (xs.length + 1)) ps)
    (step : ∀ b (i len : Nat) (h : i < len) (hxs : len = xs.size),
        let h : i < xs.toList.length := by simpa [hxs] using h
        ⦃inv.1 (b, ⟨xs.toList, i, by omega⟩)}
        f b xs[i]
        ⦃(fun b' => inv.1 (b', ⟨xs.toList, i + 1, by omega⟩), inv.2)}) :
    ⦃inv.1 (init, ⟨xs.toList, 0, by omega⟩)} Array.foldlM f init xs ⦃(fun b => inv.1 (b, ⟨xs.toList, Fin.last xs.toList.length, by omega⟩), inv.2)} := by
  cases xs
  simp only [List.foldlM_toArray]
  apply Spec.foldlM_list inv step
