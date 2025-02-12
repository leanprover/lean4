/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.TakeDrop
import Init.Data.List.Attach

/-!
# Lemmas about `List.mapM` and `List.forM`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Monadic operations -/

-- We may want to replace these `simp` attributes with explicit equational lemmas,
-- as we already have for all the non-monadic functions.
attribute [simp] mapA forA filterAuxM firstM anyM allM findM? findSomeM?

-- Previously `mapM.loop`, `filterMapM.loop`, `forIn.loop`, `forIn'.loop`
-- had attribute `@[simp]`.
-- We don't currently provide simp lemmas,
-- as this is an internal implementation and they don't seem to be needed.

/-! ### mapM -/

/-- Alternate (non-tail-recursive) form of mapM for proofs.

Note that we can not have this as the main definition and replace it using a `@[csimp]` lemma,
because they are only equal when `m` is a `LawfulMonad`.
-/
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | a :: l => return (← f a) :: (← l.mapM' f)

@[simp] theorem mapM'_nil [Monad m] {f : α → m β} : mapM' f [] = pure [] := rfl
@[simp] theorem mapM'_cons [Monad m] {f : α → m β} :
    mapM' f (a :: l) = return ((← f a) :: (← l.mapM' f)) :=
  rfl

theorem mapM'_eq_mapM [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    mapM' f l = mapM f l := by simp [go, mapM] where
  go : ∀ l acc, mapM.loop f l acc = return acc.reverse ++ (← mapM' f l)
    | [], acc => by simp [mapM.loop, mapM']
    | a::l, acc => by simp [go l, mapM.loop, mapM']

@[simp] theorem mapM_nil [Monad m] (f : α → m β) : [].mapM f = pure [] := rfl

@[simp] theorem mapM_cons [Monad m] [LawfulMonad m] (f : α → m β) :
    (a :: l).mapM f = (return (← f a) :: (← l.mapM f)) := by simp [← mapM'_eq_mapM, mapM']

@[simp] theorem mapM_id {l : List α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l <;> simp_all

@[simp] theorem mapM_append [Monad m] [LawfulMonad m] (f : α → m β) {l₁ l₂ : List α} :
    (l₁ ++ l₂).mapM f = (return (← l₁.mapM f) ++ (← l₂.mapM f)) := by induction l₁ <;> simp [*]

/-- Auxiliary lemma for `mapM_eq_reverse_foldlM_cons`. -/
theorem foldlM_cons_eq_append [Monad m] [LawfulMonad m] (f : α → m β) (as : List α) (b : β) (bs : List β) :
    (as.foldlM (init := b :: bs) fun acc a => return ((← f a) :: acc)) =
      (· ++ b :: bs) <$> as.foldlM (init := []) fun acc a => return ((← f a) :: acc) := by
  induction as generalizing b bs with
  | nil => simp
  | cons a as ih =>
    simp only [bind_pure_comp] at ih
    simp [ih, _root_.map_bind, Functor.map_map, Function.comp_def]

theorem mapM_eq_reverse_foldlM_cons [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    mapM f l = reverse <$> (l.foldlM (fun acc a => return ((← f a) :: acc)) []) := by
  rw [← mapM'_eq_mapM]
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [mapM'_cons, ih, bind_map_left, foldlM_cons, LawfulMonad.bind_assoc, pure_bind,
      foldlM_cons_eq_append, _root_.map_bind, Functor.map_map, Function.comp_def, reverse_append,
      reverse_cons, reverse_nil, nil_append, singleton_append]
    simp [bind_pure_comp]

/-! ### filterMapM -/

@[simp] theorem filterMapM_nil [Monad m] (f : α → m (Option β)) : [].filterMapM f = pure [] := rfl

theorem filterMapM_loop_eq [Monad m] [LawfulMonad m]
    (f : α → m (Option β)) (l : List α) (acc : List β) :
    filterMapM.loop f l acc = (acc.reverse ++ ·) <$> filterMapM.loop f l [] := by
  induction l generalizing acc with
  | nil => simp [filterMapM.loop]
  | cons a l ih =>
    simp only [filterMapM.loop, _root_.map_bind]
    congr
    funext b?
    split <;> rename_i b
    · apply ih
    · rw [ih, ih [b]]
      simp

@[simp] theorem filterMapM_cons [Monad m] [LawfulMonad m] (f : α → m (Option β)) :
    (a :: l).filterMapM f = do
      match (← f a) with
      | none => filterMapM f l
      | some b => return (b :: (← filterMapM f l)) := by
  conv => lhs; unfold filterMapM; unfold filterMapM.loop
  congr
  funext b?
  split <;> rename_i b
  · simp [filterMapM]
  · simp only [bind_pure_comp]
    rw [filterMapM_loop_eq, filterMapM]
    simp

/-! ### flatMapM -/

@[simp] theorem flatMapM_nil [Monad m] (f : α → m (List β)) : [].flatMapM f = pure [] := rfl

theorem flatMapM_loop_eq [Monad m] [LawfulMonad m] (f : α → m (List β)) (l : List α) (acc : List (List β)) :
    flatMapM.loop f l acc = (acc.reverse.flatten ++ ·) <$> flatMapM.loop f l [] := by
  induction l generalizing acc with
  | nil => simp [flatMapM.loop]
  | cons a l ih =>
    simp only [flatMapM.loop, append_nil, _root_.map_bind]
    congr
    funext bs
    rw [ih, ih [bs]]
    simp

@[simp] theorem flatMapM_cons [Monad m] [LawfulMonad m] (f : α → m (List β)) :
    (a :: l).flatMapM f = do
      let bs ← f a
      return (bs ++ (← l.flatMapM f)) := by
  conv => lhs; unfold flatMapM; unfold flatMapM.loop
  congr
  funext bs
  rw [flatMapM_loop_eq, flatMapM]
  simp

/-! ### foldlM and foldrM -/

theorem foldlM_map [Monad m] (f : β₁ → β₂) (g : α → β₂ → m α) (l : List β₁) (init : α) :
    (l.map f).foldlM g init = l.foldlM (fun x y => g x (f y)) init := by
  induction l generalizing g init <;> simp [*]

theorem foldrM_map [Monad m] [LawfulMonad m] (f : β₁ → β₂) (g : β₂ → α → m α) (l : List β₁)
    (init : α) : (l.map f).foldrM g init = l.foldrM (fun x y => g (f x) y) init := by
  induction l generalizing g init <;> simp [*]

theorem foldlM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : γ → β → m γ) (l : List α) (init : γ) :
    (l.filterMap f).foldlM g init =
      l.foldlM (fun x y => match f y with | some b => g x b | none => pure x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMap_cons, foldlM_cons]
    cases f a <;> simp [ih]

theorem foldrM_filterMap [Monad m] [LawfulMonad m] (f : α → Option β) (g : β → γ → m γ) (l : List α) (init : γ) :
    (l.filterMap f).foldrM g init =
      l.foldrM (fun x y => match f x with | some b => g b y | none => pure y) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMap_cons, foldrM_cons]
    cases f a <;> simp [ih]

theorem foldlM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : β → α → m β) (l : List α) (init : β) :
    (l.filter p).foldlM g init =
      l.foldlM (fun x y => if p y then g x y else pure x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filter_cons, foldlM_cons]
    split <;> simp [ih]

theorem foldrM_filter [Monad m] [LawfulMonad m] (p : α → Bool) (g : α → β → m β) (l : List α) (init : β) :
    (l.filter p).foldrM g init =
      l.foldrM (fun x y => if p x then g x y else pure y) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [filter_cons, foldrM_cons]
    split <;> simp [ih]

@[simp] theorem foldlM_attachWith [Monad m]
    (l : List α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : β → { x // q x} → m β} {b} :
    (l.attachWith q H).foldlM f b = l.attach.foldlM (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, foldlM_map]

@[simp] theorem foldrM_attachWith [Monad m] [LawfulMonad m]
    (l : List α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : { x // q x} → β → m β} {b} :
    (l.attachWith q H).foldrM f b = l.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, foldrM_map]

/-! ### forM -/

@[deprecated forM_nil (since := "2025-01-31")]
theorem forM_nil' [Monad m] : ([] : List α).forM f = (pure .unit : m PUnit) := rfl

@[deprecated forM_cons (since := "2025-01-31")]
theorem forM_cons' [Monad m] :
    (a::as).forM f = (f a >>= fun _ => as.forM f : m PUnit) :=
  List.forM_cons _ _ _

@[simp] theorem forM_append [Monad m] [LawfulMonad m] (l₁ l₂ : List α) (f : α → m PUnit) :
    forM (l₁ ++ l₂) f = (do forM l₁ f; forM l₂ f) := by
  induction l₁ <;> simp [*]

@[simp] theorem forM_map [Monad m] [LawfulMonad m] (l : List α) (g : α → β) (f : β → m PUnit) :
    forM (l.map g) f = forM l (fun a => f (g a)) := by
  induction l <;> simp [*]

/-! ### forIn' -/

theorem forIn'_loop_congr [Monad m] {as bs : List α}
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    {b : β} (ha : ∃ ys, ys ++ xs = as) (hb : ∃ ys, ys ++ xs = bs)
    (h : ∀ a m m' b, f a m b = g a m' b) : forIn'.loop as f xs b ha = forIn'.loop bs g xs b hb  := by
  induction xs generalizing b with
  | nil => simp [forIn'.loop]
  | cons a xs ih =>
    simp only [forIn'.loop] at *
    congr 1
    · rw [h]
    · funext s
      obtain b | b := s
      · rfl
      · simp
        rw [ih]

@[simp] theorem forIn'_cons [Monad m] {a : α} {as : List α}
    (f : (a' : α) → a' ∈ a :: as → β → m (ForInStep β)) (b : β) :
    forIn' (a::as) b f = f a (mem_cons_self a as) b >>=
      fun | ForInStep.done b => pure b | ForInStep.yield b => forIn' as b fun a' m b => f a' (mem_cons_of_mem a m) b := by
  simp only [forIn', List.forIn', forIn'.loop]
  congr 1
  funext s
  obtain b | b := s
  · rfl
  · apply forIn'_loop_congr
    intros
    rfl

@[simp] theorem forIn_cons [Monad m] (f : α → β → m (ForInStep β)) (a : α) (as : List α) (b : β) :
    forIn (a::as) b f = f a b >>= fun | ForInStep.done b => pure b | ForInStep.yield b => forIn as b f := by
  have := forIn'_cons (a := a) (as := as) (fun a' _ b => f a' b) b
  simpa only [forIn'_eq_forIn]

@[congr] theorem forIn'_congr [Monad m] {as bs : List α} (w : as = bs)
    {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  induction bs generalizing as b b' with
  | nil =>
    subst w
    simp [hb, forIn'_nil]
  | cons b bs ih =>
    cases as with
    | nil => simp at w
    | cons a as =>
      simp only [cons.injEq] at w
      obtain ⟨rfl, rfl⟩ := w
      simp only [forIn'_cons]
      congr 1
      · simp [h, hb]
      · funext s
        obtain b | b := s
        · rfl
        · simp
          rw [ih rfl rfl]
          intro a m b
          exact h a (mem_cons_of_mem _ m) b

/--
We can express a for loop over a list as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn'_eq_foldlM [Monad m] [LawfulMonad m]
    (l : List α) (f : (a : α) → a ∈ l → β → m (ForInStep β)) (init : β) :
    forIn' l init f = ForInStep.value <$>
      l.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [forIn'_cons, attach_cons, foldlM_cons, _root_.map_bind]
    congr 1
    funext x
    match x with
    | .done b =>
      clear ih
      dsimp
      induction as with
      | nil => simp
      | cons a as ih =>
        simp only [attach_cons, map_cons, map_map, Function.comp_def, foldlM_cons, pure_bind]
        specialize ih (fun a m b => f a (by
          simp only [mem_cons] at m
          rcases m with rfl|m
          · apply mem_cons_self
          · exact mem_cons_of_mem _ (mem_cons_of_mem _ m)) b)
        simp [ih, List.foldlM_map]
    | .yield b =>
      simp [ih, List.foldlM_map]

/-- We can express a for loop over a list which always yields as a fold. -/
@[simp] theorem forIn'_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : List α) (f : (a : α) → a ∈ l → β → m γ) (g : (a : α) → a ∈ l → β → γ → β) (init : β) :
    forIn' l init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      l.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  simp only [forIn'_eq_foldlM]
  generalize l.attach = l'
  induction l' generalizing init <;> simp_all

theorem forIn'_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : List α) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' l init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  simp only [forIn'_eq_foldlM]
  generalize l.attach = l'
  induction l' generalizing init <;> simp_all

@[simp] theorem forIn'_yield_eq_foldl
    (l : List α) (f : (a : α) → a ∈ l → β → β) (init : β) :
    forIn' (m := Id) l init (fun a m b => .yield (f a m b)) =
      l.attach.foldl (fun b ⟨a, h⟩ => f a h b) init := by
  simp only [forIn'_eq_foldlM]
  generalize l.attach = l'
  induction l' generalizing init <;> simp_all

@[simp] theorem forIn'_map [Monad m] [LawfulMonad m]
    (l : List α) (g : α → β) (f : (b : β) → b ∈ l.map g → γ → m (ForInStep γ)) :
    forIn' (l.map g) init f = forIn' l init fun a h y => f (g a) (mem_map_of_mem g h) y := by
  induction l generalizing init <;> simp_all

/--
We can express a for loop over a list as a fold,
in which whenever we reach `.done b` we keep that value through the rest of the fold.
-/
theorem forIn_eq_foldlM [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (init : β) (l : List α) :
    forIn l init f = ForInStep.value <$>
      l.foldlM (fun b a => match b with
        | .yield b => f a b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [foldlM_cons, bind_pure_comp, forIn_cons, _root_.map_bind]
    congr 1
    funext x
    match x with
    | .done b =>
      clear ih
      dsimp
      induction as with
      | nil => simp
      | cons a as ih => simp [ih]
    | .yield b =>
      simp [ih]

/-- We can express a for loop over a list which always yields as a fold. -/
@[simp] theorem forIn_yield_eq_foldlM [Monad m] [LawfulMonad m]
    (l : List α) (f : α → β → m γ) (g : α → β → γ → β) (init : β) :
    forIn l init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      l.foldlM (fun b a => g a b <$> f a b) init := by
  simp only [forIn_eq_foldlM]
  induction l generalizing init <;> simp_all

theorem forIn_pure_yield_eq_foldl [Monad m] [LawfulMonad m]
    (l : List α) (f : α → β → β) (init : β) :
    forIn l init (fun a b => pure (.yield (f a b))) =
      pure (f := m) (l.foldl (fun b a => f a b) init) := by
  simp only [forIn_eq_foldlM]
  induction l generalizing init <;> simp_all

@[simp] theorem forIn_yield_eq_foldl
    (l : List α) (f : α → β → β) (init : β) :
    forIn (m := Id) l init (fun a b => .yield (f a b)) =
      l.foldl (fun b a => f a b) init := by
  simp only [forIn_eq_foldlM]
  induction l generalizing init <;> simp_all

@[simp] theorem forIn_map [Monad m] [LawfulMonad m]
    (l : List α) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (l.map g) init f = forIn l init fun a y => f (g a) y := by
  induction l generalizing init <;> simp_all

/-! ### allM -/

theorem allM_eq_not_anyM_not [Monad m] [LawfulMonad m] (p : α → m Bool) (as : List α) :
    allM p as = (! ·) <$> anyM ((! ·) <$> p ·) as := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [allM, anyM, bind_map_left, _root_.map_bind]
    congr
    funext b
    split <;> simp_all

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldlM_subtype [Monad m] {p : α → Prop} {l : List { x // p x }}
    {f : β → { x // p x } → m β} {g : β → α → m β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
    l.foldlM f x = l.unattach.foldlM g x := by
  unfold unattach
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, hf]

@[wf_preprocess] theorem foldlM_wfParam [Monad m] (xs : List α) (f : β → α → m β) :
    (wfParam xs).foldlM f = xs.attach.unattach.foldlM f := by
  simp [wfParam]

@[wf_preprocess] theorem foldlM_unattach [Monad m] (P : α → Prop) (xs : List (Subtype P)) (f : β → α → m β) :
    xs.unattach.foldlM f = xs.foldlM fun b ⟨x, h⟩ =>
      binderNameHint b f <| binderNameHint x (f b) <| binderNameHint h () <|
      f b (wfParam x) := by
  simp [wfParam]

/--
This lemma identifies monadic folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldrM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → β → m β} {g : α → β → m β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) :
    l.foldrM f x = l.unattach.foldrM g x := by
  unfold unattach
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp [ih, hf, foldrM_cons]
    congr
    funext b
    simp [hf]

@[wf_preprocess] theorem foldrM_wfParam [Monad m] [LawfulMonad m] (xs : List α) (f : α → β → m β) :
    (wfParam xs).foldrM f = xs.attach.unattach.foldrM f := by
  simp [wfParam]

@[wf_preprocess] theorem foldrM_unattach [Monad m] [LawfulMonad m] (P : α → Prop) (xs : List (Subtype P)) (f : α → β → m β) :
    xs.unattach.foldrM f = xs.foldrM fun ⟨x, h⟩ b =>
      binderNameHint x f <| binderNameHint h () <| binderNameHint b (f x) <|
      f (wfParam x) b := by
  simp [wfParam]

/--
This lemma identifies monadic maps over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem mapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → m β} {g : α → m β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.mapM f = l.unattach.mapM g := by
  unfold unattach
  simp [← List.mapM'_eq_mapM]
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf]

@[wf_preprocess] theorem mapM_wfParam [Monad m] [LawfulMonad m] (xs : List α) (f : α → m β) :
    (wfParam xs).mapM f = xs.attach.unattach.mapM f := by
  simp [wfParam]

@[wf_preprocess] theorem mapM_unattach [Monad m] [LawfulMonad m] (P : α → Prop) (xs : List (Subtype P)) (f : α → m β) :
    xs.unattach.mapM f = xs.mapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem filterMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → m (Option β)} {g : α → m (Option β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.filterMapM f = l.unattach.filterMapM g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf, filterMapM_cons]

@[wf_preprocess] theorem filterMapM_wfParam [Monad m] [LawfulMonad m]
    (xs : List α) (f : α → m (Option β)) :
    (wfParam xs).filterMapM f = xs.attach.unattach.filterMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem filterMapM_unattach [Monad m] [LawfulMonad m]
    (P : α → Prop) (xs : List (Subtype P)) (f : α → m (Option β)) :
    xs.unattach.filterMapM f = xs.filterMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

@[simp] theorem flatMapM_subtype [Monad m] [LawfulMonad m] {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → m (List β)} {g : α → m (List β)} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (l.flatMapM f) = l.unattach.flatMapM g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf]

@[wf_preprocess] theorem flatMapM_wfParam [Monad m] [LawfulMonad m]
    (xs : List α) (f : α → m (List β)) :
    (wfParam xs).flatMapM f = xs.attach.unattach.flatMapM f := by
  simp [wfParam]

@[wf_preprocess] theorem flatMapM_unattach [Monad m] [LawfulMonad m]
    (P : α → Prop) (xs : List (Subtype P)) (f : α → m (List β)) :
    xs.unattach.flatMapM f = xs.flatMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

end List
