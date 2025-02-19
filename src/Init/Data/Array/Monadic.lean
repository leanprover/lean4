/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach
import Init.Data.List.Monadic

/-!
# Lemmas about `Array.forIn'` and `Array.forIn`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open Nat

/-! ## Monadic operations -/

/-! ### mapM -/

@[simp] theorem mapM_append [Monad m] [LawfulMonad m] (f : α → m β) {xs ys : Array α} :
    (xs ++ ys).mapM f = (return (← xs.mapM f) ++ (← ys.mapM f)) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

theorem mapM_eq_foldlM_push [Monad m] [LawfulMonad m] (f : α → m β) (xs : Array α) :
    mapM f xs = xs.foldlM (fun acc a => return (acc.push (← f a))) #[] := by
  rcases xs with ⟨xs⟩
  simp only [List.mapM_toArray, bind_pure_comp, List.size_toArray, List.foldlM_toArray']
  rw [List.mapM_eq_reverse_foldlM_cons]
  simp only [bind_pure_comp, Functor.map_map]
  suffices ∀ (l), (fun l' => l'.reverse.toArray) <$> List.foldlM (fun acc a => (fun a => a :: acc) <$> f a) l xs =
      List.foldlM (fun acc a => acc.push <$> f a) l.reverse.toArray xs by
    exact this []
  intro l
  induction xs generalizing l with
  | nil => simp
  | cons a as ih =>
    simp [ih, List.foldlM_cons]

/-! ### foldlM and foldrM -/

theorem foldlM_map [Monad m] (f : β₁ → β₂) (g : α → β₂ → m α) (xs : Array β₁) (init : α) (w : stop = xs.size) :
    (xs.map f).foldlM g init 0 stop = xs.foldlM (fun x y => g x (f y)) init 0 stop := by
  subst w
  cases xs
  simp [List.foldlM_map]

theorem foldrM_map [Monad m] [LawfulMonad m] (f : β₁ → β₂) (g : β₂ → α → m α) (xs : Array β₁)
    (init : α) (w : start = xs.size) :
    (xs.map f).foldrM g init start 0 = xs.foldrM (fun x y => g (f x) y) init start 0 := by
  subst w
  cases xs
  simp [List.foldrM_map]

theorem foldlM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : γ → β → m γ)
    (xs : Array α) (init : γ) (w : stop = (xs.filterMap f).size) :
    (xs.filterMap f).foldlM g init 0 stop =
      xs.foldlM (fun x y => match f y with | some b => g x b | none => pure x) init := by
  subst w
  cases xs
  simp [List.foldlM_filterMap]
  rfl

theorem foldrM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : β → γ → m γ)
    (xs : Array α) (init : γ) (w : start = (xs.filterMap f).size) :
    (xs.filterMap f).foldrM g init start 0 =
      xs.foldrM (fun x y => match f x with | some b => g b y | none => pure y) init := by
  subst w
  cases xs
  simp [List.foldrM_filterMap]
  rfl

theorem foldlM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : β → α → m β)
    (xs : Array α) (init : β) (w : stop = (xs.filter p).size) :
    (xs.filter p).foldlM g init 0 stop =
      xs.foldlM (fun x y => if p y then g x y else pure x) init := by
  subst w
  cases xs
  simp [List.foldlM_filter]

theorem foldrM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : α → β → m β)
    (xs : Array α) (init : β) (w : start = (xs.filter p).size) :
    (xs.filter p).foldrM g init start 0 =
      xs.foldrM (fun x y => if p x then g x y else pure y) init := by
  subst w
  cases xs
  simp [List.foldrM_filter]

@[simp] theorem foldlM_attachWith [Monad m]
    (xs : Array α) {q : α → Prop} (H : ∀ a, a ∈ xs → q a) {f : β → { x // q x} → m β} {b} (w : stop = xs.size):
    (xs.attachWith q H).foldlM f b 0 stop =
      xs.attach.foldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.foldlM_map]

@[simp] theorem foldrM_attachWith [Monad m] [LawfulMonad m]
    (xs : Array α) {q : α → Prop} (H : ∀ a, a ∈ xs → q a) {f : { x // q x} → β → m β} {b} (w : start = xs.size):
    (xs.attachWith q H).foldrM f b start 0 =
      xs.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.foldrM_map]

/-! ### forM -/

@[congr] theorem forM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {f : α → m PUnit} :
    forM as f = forM bs f := by
  cases as <;> cases bs
  simp_all

@[simp] theorem forM_append [Monad m] [LawfulMonad m] (xs ys : Array α) (f : α → m PUnit) :
    forM (xs ++ ys) f = (do forM xs f; forM ys f) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

@[simp] theorem forM_map [Monad m] [LawfulMonad m] (xs : Array α) (g : α → β) (f : β → m PUnit) :
    forM (xs.map g) f = forM xs (fun a => f (g a)) := by
  rcases xs with ⟨xs⟩
  simp

/-! ### forIn' -/

@[congr] theorem forIn'_congr [Monad m] {as bs : Array α} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  cases as <;> cases bs
  simp only [mk.injEq, mem_toArray, List.forIn'_toArray] at w h ⊢
  exact List.forIn'_congr w hb h

/--
We can express a for loop over an array as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn'_eq_foldlM [Monad m] [LawfulMonad m]
    (xs : Array α) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (init : β) :
    forIn' xs init f = ForInStep.value <$>
      xs.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases xs with ⟨xs⟩
  simp [List.forIn'_eq_foldlM, List.foldlM_map]
  congr

/-- We can express a for loop over an array which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (xs : Array α) (f : (a : α) → a ∈ xs → β → m γ) (g : (a : α) → a ∈ xs → β → γ → β) (init : β) :
    forIn' xs init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      xs.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  rcases xs with ⟨xs⟩
  simp [List.foldlM_map]

theorem forIn'_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (xs : Array α) (f : (a : α) → a ∈ xs → β → β) (init : β) :
    forIn' xs init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (xs.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  rcases xs with ⟨xs⟩
  simp [List.forIn'_pure_yield_eq_foldl, List.foldl_map]

@[simp] theorem forIn'_yield_eq_foldl
    (xs : Array α) (f : (a : α) → a ∈ xs → β → β) (init : β) :
    forIn' (m := Id) xs init (fun a m b => .yield (f a m b)) =
      xs.attach.foldl (fun b ⟨a, h⟩ => f a h b) init := by
  rcases xs with ⟨xs⟩
  simp [List.foldl_map]

@[simp] theorem forIn'_map [Monad m] [LawfulMonad m]
    (xs : Array α) (g : α → β) (f : (b : β) → b ∈ xs.map g → γ → m (ForInStep γ)) :
    forIn' (xs.map g) init f = forIn' xs init fun a h y => f (g a) (mem_map_of_mem g h) y := by
  rcases xs with ⟨xs⟩
  simp

/--
We can express a for loop over an array as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn_eq_foldlM [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (init : β) (xs : Array α) :
    forIn xs init f = ForInStep.value <$>
      xs.foldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  rcases xs with ⟨xs⟩
  simp only [List.forIn_toArray, List.forIn_eq_foldlM, List.size_toArray, List.foldlM_toArray']
  congr

/-- We can express a for loop over an array which always yields as a fold. -/
@[simp] theorem forIn_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (xs : Array α) (f : α → β → m γ) (g : α → β → γ → β) (init : β) :
    forIn xs init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      xs.foldlM (fun b a => g a b <$> f a b) init := by
  rcases xs with ⟨xs⟩
  simp [List.foldlM_map]

theorem forIn_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (xs : Array α) (f : α → β → β) (init : β) :
    forIn xs init (fun a b => pure (.yield (f a b))) =
      pure (f := m) (xs.foldl (fun b a => f a b) init) := by
  rcases xs with ⟨xs⟩
  simp [List.forIn_pure_yield_eq_foldl, List.foldl_map]

@[simp] theorem forIn_yield_eq_foldl
    (xs : Array α) (f : α → β → β) (init : β) :
    forIn (m := Id) xs init (fun a b => .yield (f a b)) =
      xs.foldl (fun b a => f a b) init := by
  rcases xs with ⟨xs⟩
  simp [List.foldl_map]

@[simp] theorem forIn_map [Monad m] [LawfulMonad m]
    (xs : Array α) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (xs.map g) init f = forIn xs init fun a y => f (g a) y := by
  rcases xs with ⟨xs⟩
  simp

end Array

namespace List

theorem filterM_toArray [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) :
    l.toArray.filterM p = toArray <$> l.filterM p := by
  simp only [Array.filterM, filterM, foldlM_toArray, bind_pure_comp, Functor.map_map]
  conv => lhs; rw [← reverse_nil]
  generalize [] = acc
  induction l generalizing acc with simp
  | cons x xs ih =>
    congr; funext b
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, cond_false]
      exact ih acc
    · simp only [↓reduceIte, ← reverse_cons, pure_bind, cond_true]
      exact ih (x :: acc)

/-- Variant of `filterM_toArray` with a side condition for the stop position. -/
@[simp] theorem filterM_toArray' [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) (w : stop = l.length) :
    l.toArray.filterM p 0 stop = toArray <$> l.filterM p := by
  subst w
  rw [filterM_toArray]

theorem filterRevM_toArray [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) :
    l.toArray.filterRevM p = toArray <$> l.filterRevM p := by
  simp [Array.filterRevM, filterRevM]
  rw [← foldlM_reverse, ← foldlM_toArray, ← Array.filterM, filterM_toArray]
  simp only [filterM, bind_pure_comp, Functor.map_map, reverse_toArray, reverse_reverse]

/-- Variant of `filterRevM_toArray` with a side condition for the start position. -/
@[simp] theorem filterRevM_toArray' [Monad m] [LawfulMonad m] (l : List α) (p : α → m Bool) (w : start = l.length) :
    l.toArray.filterRevM p start 0 = toArray <$> l.filterRevM p := by
  subst w
  rw [filterRevM_toArray]

theorem filterMapM_toArray [Monad m] [LawfulMonad m] (l : List α) (f : α → m (Option β)) :
    l.toArray.filterMapM f = toArray <$> l.filterMapM f := by
  simp [Array.filterMapM, filterMapM]
  conv => lhs; rw [← reverse_nil]
  generalize [] = acc
  induction l generalizing acc with simp [filterMapM.loop]
  | cons x xs ih =>
    congr; funext o
    cases o
    · simp only [pure_bind]; exact ih acc
    · simp only [pure_bind]; rw [← List.reverse_cons]; exact ih _

/-- Variant of `filterMapM_toArray` with a side condition for the stop position. -/
@[simp] theorem filterMapM_toArray' [Monad m] [LawfulMonad m] (l : List α) (f : α → m (Option β)) (w : stop = l.length) :
    l.toArray.filterMapM f 0 stop = toArray <$> l.filterMapM f := by
  subst w
  rw [filterMapM_toArray]

@[simp] theorem flatMapM_toArray [Monad m] [LawfulMonad m] (l : List α) (f : α → m (Array β)) :
    l.toArray.flatMapM f = toArray <$> l.flatMapM (fun a => Array.toList <$> f a) := by
  simp only [Array.flatMapM, bind_pure_comp, foldlM_toArray, flatMapM]
  conv => lhs; arg 2; change [].reverse.flatten.toArray
  generalize [] = acc
  induction l generalizing acc with
  | nil => simp only [foldlM_nil, flatMapM.loop, map_pure]
  | cons x xs ih =>
    simp only [foldlM_cons, bind_map_left, flatMapM.loop, _root_.map_bind]
    congr; funext xs
    conv => lhs; rw [Array.toArray_append, ← flatten_concat, ← reverse_cons]
    exact ih _

end List

namespace Array

@[congr] theorem filterM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {p : α → m Bool} {q : α → m Bool} (h : ∀ a, p a = q a) :
    as.filterM p = bs.filterM q := by
  subst w
  simp [filterM, h]

@[congr] theorem filterRevM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {p : α → m Bool} {q : α → m Bool} (h : ∀ a, p a = q a) :
    as.filterRevM p = bs.filterRevM q := by
  subst w
  simp [filterRevM, h]

@[congr] theorem filterMapM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {f : α → m (Option β)} {g : α → m (Option β)} (h : ∀ a, f a = g a) :
    as.filterMapM f = bs.filterMapM g := by
  subst w
  simp [filterMapM, h]

@[congr] theorem flatMapM_congr [Monad m] {as bs : Array α} (w : as = bs)
    {f : α → m (Array β)} {g : α → m (Array β)} (h : ∀ a, f a = g a) :
    as.flatMapM f = bs.flatMapM g := by
  subst w
  simp [flatMapM, h]

theorem toList_filterM [Monad m] [LawfulMonad m] (xs : Array α) (p : α → m Bool) :
    toList <$> xs.filterM p = xs.toList.filterM p := by
  rw [List.filterM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_filterRevM [Monad m] [LawfulMonad m] (xs : Array α) (p : α → m Bool) :
    toList <$> xs.filterRevM p = xs.toList.filterRevM p := by
  rw [List.filterRevM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_filterMapM [Monad m] [LawfulMonad m] (xs : Array α) (f : α → m (Option β)) :
    toList <$> xs.filterMapM f = xs.toList.filterMapM f := by
  rw [List.filterMapM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_flatMapM [Monad m] [LawfulMonad m] (xs : Array α) (f : α → m (Array β)) :
    toList <$> xs.flatMapM f = xs.toList.flatMapM (fun a => toList <$> f a) := by
  rw [List.flatMapM_toArray]
  simp only [Functor.map_map, id_map']

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldlM_subtype [Monad m] {p : α → Prop} {xs : Array { x // p x }}
    {f : β → { x // p x } → m β} {g : β → α → m β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) (w : stop = xs.size) :
    xs.foldlM f x 0 stop = xs.unattach.foldlM g x 0 stop := by
  subst w
  rcases xs with ⟨l⟩
  simp
  rw [List.foldlM_subtype hf]

@[wf_preprocess] theorem foldlM_wfParam [Monad m] (xs : Array α) (f : β → α → m β) :
    (wfParam xs).foldlM f = xs.attach.unattach.foldlM f := by
  simp [wfParam]

@[wf_preprocess] theorem foldlM_unattach [Monad m] (P : α → Prop) (xs : Array (Subtype P)) (f : β → α → m β) :
    xs.unattach.foldlM f = xs.foldlM fun b ⟨x, h⟩ =>
      binderNameHint b f <| binderNameHint x (f b) <| binderNameHint h () <|
      f b (wfParam x) := by
  simp [wfParam]

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldrM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {xs : Array { x // p x }}
    {f : { x // p x } → β → m β} {g : α → β → m β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) (w : start = xs.size) :
    xs.foldrM f x start 0 = xs.unattach.foldrM g x start 0:= by
  subst w
  rcases xs with ⟨xs⟩
  simp
  rw [List.foldrM_subtype hf]


@[wf_preprocess] theorem foldrM_wfParam [Monad m] [LawfulMonad m] (xs : Array α) (f : α → β → m β) :
    (wfParam xs).foldrM f = xs.attach.unattach.foldrM f := by
  simp [wfParam]

@[wf_preprocess] theorem foldrM_unattach [Monad m] [LawfulMonad m] (P : α → Prop) (xs : Array (Subtype P)) (f : α → β → m β) :
    xs.unattach.foldrM f = xs.foldrM fun ⟨x, h⟩ b =>
      binderNameHint x f <| binderNameHint h () <| binderNameHint b (f x) <|
      f (wfParam x) b := by
  simp [wfParam]

/--
This lemma identifies monadic maps over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem mapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {xs : Array { x // p x }}
    {f : { x // p x } → m β} {g : α → m β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.mapM f = xs.unattach.mapM g := by
  rcases xs with ⟨xs⟩
  simp
  rw [List.mapM_subtype hf]

@[wf_preprocess] theorem mapM_wfParam [Monad m] [LawfulMonad m] (xs : Array α) (f : α → m β) :
    (wfParam xs).mapM f = xs.attach.unattach.mapM f := by
  simp [wfParam]

@[wf_preprocess] theorem mapM_unattach [Monad m] [LawfulMonad m] (P : α → Prop) (xs : Array (Subtype P)) (f : α → m β) :
    xs.unattach.mapM f = xs.mapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem filterMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {xs : Array { x // p x }}
    {f : { x // p x } → m (Option β)} {g : α → m (Option β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) (w : stop = xs.size) :
    xs.filterMapM f 0 stop = xs.unattach.filterMapM g := by
  subst w
  rcases xs with ⟨xs⟩
  simp
  rw [List.filterMapM_subtype hf]


@[wf_preprocess] theorem filterMapM_wfParam [Monad m] [LawfulMonad m]
    (xs : Array α) (f : α → m (Option β)) :
    (wfParam xs).filterMapM f = xs.attach.unattach.filterMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem filterMapM_unattach [Monad m] [LawfulMonad m]
    (P : α → Prop) (xs : Array (Subtype P)) (f : α → m (Option β)) :
    xs.unattach.filterMapM f = xs.filterMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem flatMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {xs : Array { x // p x }}
    {f : { x // p x } → m (Array β)} {g : α → m (Array β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (xs.flatMapM f) = xs.unattach.flatMapM g := by
  rcases xs with ⟨xs⟩
  simp
  rw [List.flatMapM_subtype]
  simp [hf]

@[wf_preprocess] theorem flatMapM_wfParam [Monad m] [LawfulMonad m]
    (xs : Array α) (f : α → m (Array β)) :
    (wfParam xs).flatMapM f = xs.attach.unattach.flatMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem flatMapM_unattach [Monad m] [LawfulMonad m]
    (P : α → Prop) (xs : Array (Subtype P)) (f : α → m (Array β)) :
    xs.unattach.flatMapM f = xs.flatMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

end Array
