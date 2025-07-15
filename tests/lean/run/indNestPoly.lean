
opaque T : Type u → Type u

/--
error: (kernel) arg #1 of 'S'.node' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive S' where
  | empty : S'
  | node (cs : T S') : S'

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


inductive S.Raw where
  | empty : S.Raw
  -- | node (cs : TP.apply S.Raw) : S.Raw
  | node (cs : Σ x : TP.A, (TP.B x → S.Raw)) : S.Raw

def S := S.Raw

-- Fake constructors
noncomputable def S.empty : S := S.Raw.empty
noncomputable def S.node (cs : T S) : S := S.Raw.node cs.repr

-- Fake casesOn
noncomputable def S.casesOn' (motive : S → Sort u)
  (empty : motive S.empty)
  (node : (cs : T S) → motive (S.node cs)) (s : S) : motive s :=
  match s with
  | S.Raw.empty => empty
  | S.Raw.node cs => by
    rw [← @T.repr_abs _ cs]
    apply node

theorem cast_congrArg_mk
  {T : Type w}
  {S : Type v}
  (f : T → S)
  (motive : S → Sort u)
  (g : (node : T) → motive (f node))
  (m n : T) (h : m = n) : cast (congrArg (fun x => motive (f x)) h) (g m) = g n := by
  cases h
  rfl

theorem S.casesOn'_eq1 motive empty node :
    S.casesOn' motive empty node S.empty = empty := by
  rfl

theorem S.casesOn'_eq2 motive empty node cs :
    S.casesOn' motive empty node (S.node cs) = node cs := by
  unfold S.casesOn' S.node
  dsimp only
  apply cast_congrArg_mk
  simp [T.abs_repr]
