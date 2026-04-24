/-
Experiment: can we define `extrinsicRepeat` using a `Pred`/`fix'`/`fix` pattern
(making it computable without `@[implemented_by opaqueRepeat]`) while keeping
the *pointwise* `IsRepeatFixAt` termination notion that the original
`extrinsicRepeat` uses?

Conclusion: no, not cleanly.

The abstract pattern works for a **global** fixpoint `∃ f, F f = f` because every
recursive call can lean on the uniform witness `h.choose`. With pointwise
`IsRepeatFixAt`, each recursive call at a yielded `x` would use `x`'s own least
witness, which generally differs from `a`'s. The body of the `fix'`-style
partial def at `a` is `repeatF f (extrinsicRepeat' f · |>.val) a`; proving the
subtype obligation would require, after rewriting with `IsRepeatFixAt f a nn`,
showing pointwise at every yielded `x` that
  `Nat.repeat (repeatF f) nn pure x = (extrinsicRepeat' f x).val`.
Extracting a yielded `x` from a bind equality over an arbitrary `Monad` needs
something `MonadAttach`-shaped, which we don't want to require.

This file records the attempt so we don't retry it. The provable pieces
(`extrinsicRepeat_terminates` given a pointwise `IsLeast (IsRepeatFixAt f a) n`)
compile; the obstruction is the `sorry` in `extrinsicRepeat'`.
-/

import Std

section AbstractPattern

variable {α β : Type _}

noncomputable def Pred (F : (α → β) → (α → β)) : α → β → Prop :=
  open scoped Classical in
  if h : ∃ f, F f = f then (h.choose · = ·) else (fun _ _ => True)

instance [Nonempty β] {F : (α → β) → (α → β)} : Nonempty (Subtype (Pred F a)) := by
  by_cases h : ∃ f, F f = f
  · exact ⟨⟨h.choose a, by simp [Pred, h]⟩⟩
  · exact ⟨⟨Classical.choice inferInstance, by simp [Pred, h]⟩⟩

partial def fix' [Nonempty β] (F : (α → β) → (α → β)) (a : α) : Subtype (Pred F a) :=
  ⟨F (fix' F · |>.val) a, by
    simp only [Pred]
    split <;> rename_i h
    · simp
      have h' x := (fix' F x).property
      simp [Pred, h] at h'
      simp [← h']
      have := h.choose_spec
      rw [this]
    · simp
    done⟩

/-- `fix F` is a fixpoint of `F` if one exists; otherwise an opaque function. -/
def fix [Nonempty β] (F : (α → β) → (α → β)) (a : α) : β :=
  (fix' F a).val

theorem fix_eq [Nonempty β] {F : (α → β) → (α → β)} (h : ∃ f, F f = f) :
    fix F = F (fix F) := by
  ext a
  simp [fix]
  have h' x := (fix' F x).property
  simp [Pred, h] at h'
  simp [← h']
  have := h.choose_spec
  rw [← this]
  congr 1
  ext a
  simp [fix]
  rw [h']

end AbstractPattern

variable {α : Type u} {m : Type u → Type v} [Monad m]

partial def opaqueRepeat (f : α → m (ForInStep α)) (a : α) : m α := do
  match ← f a with
    | ForInStep.done a => pure a
    | ForInStep.yield a => opaqueRepeat f a

def repeatF (f : α → m (ForInStep α)) (recur : α → m α) (a : α) : m α := do
  match ← f a with
    | ForInStep.done a => pure a
    | ForInStep.yield a => recur a

/-- Pointwise fixpoint: the `n`-th iterate stabilizes at `a`. -/
def IsRepeatFixAt (f : α → m (ForInStep α)) (a : α) (n : Nat) : Prop :=
  Nat.repeat (repeatF f) n pure a = repeatF f (Nat.repeat (repeatF f) n pure) a

def IsLeast (P : Nat → Prop) (n : Nat) : Prop := P n ∧ ∀ m, m < n → ¬ P m
def IsUnique (P : α → Prop) (n : α) : Prop := P n ∧ ∀ m, P m → m = n

open Classical in
theorem Nat.exists_IsLeast {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, IsLeast P n := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h' : ∃ m, m < n ∧ P m
    · obtain ⟨m, hmlt, hPm⟩ := h'
      exact ih m hmlt hPm
    · exact ⟨n, hn, fun m hmlt hPm => h' ⟨m, hmlt, hPm⟩⟩

theorem Nat.IsLeast_unique {P : Nat → Prop} (h : IsLeast P n) : IsUnique (IsLeast P) n := by
  refine ⟨h, ?_⟩
  rintro n' ⟨hPn', hlt'⟩
  rcases Nat.lt_trichotomy n n' with h1 | h1 | h1
  · exact absurd h.1 (hlt' n h1)
  · exact h1.symm
  · exact absurd hPn' (h.2 n' h1)

/--
Pointwise predicate: at `a`, pin the value to `Nat.repeat (repeatF f) nn pure a`
where `nn` is the least `n` with `IsRepeatFixAt f a n`, if any exists.
-/
noncomputable def PredRepeat (f : α → m (ForInStep α)) (a : α) : m α → Prop :=
  open scoped Classical in
  if h : ∃ n, IsLeast (IsRepeatFixAt f a) n then
    (Nat.repeat (repeatF f) h.choose pure a = ·)
  else
    (fun _ => True)

instance [Nonempty (m α)] {f : α → m (ForInStep α)} {a : α} :
    Nonempty (Subtype (PredRepeat f a)) := by
  by_cases h : ∃ n, IsLeast (IsRepeatFixAt f a) n
  · exact ⟨⟨Nat.repeat (repeatF f) h.choose pure a, by simp [PredRepeat, h]⟩⟩
  · exact ⟨⟨Classical.choice inferInstance, by simp [PredRepeat, h]⟩⟩

/--
The intended pointwise analogue of `fix'`. The `sorry` is the obstruction described
in the file header: `(extrinsicRepeat' f x).property` at a yielded `x` uses `x`'s
own least witness, not `a`'s, so we can't line up the continuations.
-/
partial def extrinsicRepeat' [Nonempty (m α)] (f : α → m (ForInStep α)) (a : α) :
    Subtype (PredRepeat f a) :=
  ⟨repeatF f (extrinsicRepeat' f · |>.val) a, by
    simp only [PredRepeat]
    split <;> rename_i h
    · sorry
    · simp
    done⟩

def extrinsicRepeat (f : α → m (ForInStep α)) (a : α) : m α :=
  haveI : Nonempty (m α) := ⟨pure a⟩
  (extrinsicRepeat' f a).val

/-- Provable without touching `extrinsicRepeat'`'s sorry: the termination property. -/
theorem extrinsicRepeat_terminates {f : α → m (ForInStep α)} {a : α} {n : Nat}
    (h : IsLeast (IsRepeatFixAt f a) n) :
    extrinsicRepeat f a = Nat.repeat (repeatF f) n pure a := by
  haveI : Nonempty (m α) := ⟨pure a⟩
  show (extrinsicRepeat' f a).val = Nat.repeat (repeatF f) n pure a
  have hex : ∃ n, IsLeast (IsRepeatFixAt f a) n := ⟨n, h⟩
  have hchoose : hex.choose = n := (Nat.IsLeast_unique h).2 _ hex.choose_spec
  have := (extrinsicRepeat' f a).property
  simp [PredRepeat, hex, hchoose] at this
  exact this.symm
