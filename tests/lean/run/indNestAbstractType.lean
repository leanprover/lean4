
opaque T : Type u → Type u

/--
error: (kernel) arg #1 of 'S'.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
structure S' where
  node : T S'


inductive T.Raw (α : Type u) : Type u where
  | mk : α → T.Raw α

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

theorem S.casesOn'_eq1_dep motive mk node :
    S.casesOn' motive mk (S.mk node) = mk node := by
  unfold S.casesOn' S.mk
  simp
  sorry
