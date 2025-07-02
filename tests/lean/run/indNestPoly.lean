
opaque T : Type u → Type u

/--
error: (kernel) arg #1 of 'S'.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
structure S' where
  node : T S'

structure PFunctor.{u} : Type (u+1) where
  A : Type u
  B : A → Type u

def PFunctor.apply (P : PFunctor.{u}) (α : Type u) :=
  Σ x : P.A, P.B x → α
def PFunctor.map (P : PFunctor.{u}) {α β : Type u} (g : α → β) :
    P.apply α → P.apply β :=
  fun x=> ⟨x.1, fun i => g (x.2 i)⟩

axiom TP : PFunctor.{0}

axiom T.abs : (TP.apply α) → T α
axiom T.repr : T α → (TP.apply α)
axiom T.abs_repr : T.abs (T.repr x) = x
axiom T.repr_abs : T.repr (T.abs x) = x
-- axiom T.abs_map (f : α → β) (x : T α) : T.abs (TP.map f (T.repr x)) = T.map f (T.abs x)


structure S.Raw where mk ::
  -- raw_node : TP.apply S.Raw
  raw_node : Σ x : TP.A, (TP.B x → S.Raw)

structure S where ofRaw ::
  toRaw : S.Raw

-- Fake constructor
noncomputable def S.mk (node : T S) : S where
  toRaw := S.Raw.mk (TP.map S.toRaw node.repr)

-- Fake casesOn (nondep)
noncomputable def S.casesOn' (motive : S → Sort u)
  (mk : (node : T S) → motive (S.mk node)) (s : S) : motive s :=
  match s with
  | ⟨⟨raw_node⟩⟩ => by
    specialize mk (T.abs (TP.map S.ofRaw raw_node))
    unfold S.mk at mk
    rw [T.repr_abs] at mk
    assumption

theorem S.casesOn'_eq1_nondep motive mk node :
    S.casesOn' (fun _ => motive) mk (S.mk node) = mk node := by
  unfold S.casesOn' S.mk
  dsimp
  change mk (T.abs node.repr) = mk node
  rw [T.abs_repr]

theorem S.casesOn'_eq1_dep motive mk node :
    S.casesOn' motive mk (S.mk node) = mk node := by
  unfold S.casesOn' S.mk
  dsimp only
  conv => lhs; arg 2; change mk (T.abs node.repr)
  sorry
