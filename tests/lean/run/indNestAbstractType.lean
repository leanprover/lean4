
opaque T : Type u → Type u

/--
error: (kernel) arg #1 of 'S'.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
structure S' where
  node : T S'

inductive T.Raw (α : Type u) : Type u where
  | mk : α → T.Raw α → T.Raw α -- pseudo-implementation, representative for any kernel-friendly type

axiom T.abs : T.Raw α → T α
axiom T.repr : T α → T.Raw α
axiom T.abs_repr : T.abs (T.repr x) = x
axiom T.repr_abs : T.repr (T.abs x) = x
axiom T.map {α β} : (f : α → β) → T α → T β
axiom T.map_map_id (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) (x : T α) :
  T.map g (T.map f x) = x


structure S.Raw where mk ::
  raw_node : T.Raw S.Raw

structure S where ofRaw ::
  toRaw : S.Raw

-- Fake constructor
noncomputable def S.mk (node : T S) : S where
  toRaw := S.Raw.mk (node.map S.toRaw).repr

-- Fake casesOn (nondep)
noncomputable def S.casesOn' (motive : S → Sort u)
  (mk : (node : T S) → motive (S.mk node))  (s : S) : motive s :=
  match s with
  | ⟨⟨raw_node⟩⟩ => by
    specialize mk (((T.abs raw_node).map S.ofRaw))
    unfold S.mk at mk
    rw [T.map_map_id] at mk
    case h => intro; rfl
    rw [T.repr_abs] at mk
    assumption

theorem S.casesOn'_eq1_nondep motive mk node :
    S.casesOn' (fun _ => motive) mk (S.mk node) = mk node := by
  unfold S.casesOn' S.mk
  simp
  -- simp [T.abs_repr] why does this fail?
  rw [T.abs_repr]
  rw [T.map_map_id]
  case h => intros; rfl

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), a ≍ a'
  | rfl, rfl => .rfl

theorem cast_eq_iff_heq : cast e a = a' ↔ a ≍ a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h; rfl⟩

theorem cast_congrArg_mk
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : cast (congrArg (fun x => motive (f x)) h) (g m) = g n := by
  cases h
  rfl

theorem heq_motive_f_congr
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : g m ≍ g n := by
  cases h
  rfl

theorem S.casesOn'_eq1_dep motive mk node :
    S.casesOn' motive mk (S.mk node) = mk node := by
  unfold S.casesOn' S.mk
  simp only [eq_mp_eq_cast, cast_cast, cast_eq_iff_heq]
  apply heq_motive_f_congr
  simp [T.abs_repr, T.map_map_id]

set_option linter.unusedVariables false in
axiom T.below : ∀ {α : Type u} (p : α → Sort v), T α → Sort v


/-
-- Fake recursor
noncomputable def S.rec' (motive : S → Sort u)
  (mk : (node : T S) → (h : node.below motive) → motive (S.mk node))
  (s : S) : motive s :=
  sorry
-/
