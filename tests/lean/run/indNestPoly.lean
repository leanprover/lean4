
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

-- Fake casesOn (nondep)
noncomputable def S.casesOn' (motive : S → Sort u)
  (empty : motive S.empty)
  (node : (cs : T S) → motive (S.node cs)) (s : S) : motive s :=
  match s with
  | S.Raw.empty => empty
  | S.Raw.node cs => by
    rw [← @T.repr_abs _ cs]
    apply node

theorem S.casesOn'_eq2_nondep motive empty node cs :
    S.casesOn' (fun _ => motive) empty node (S.node cs) = node cs := by
  unfold S.casesOn' S.node
  dsimp
  rw [T.abs_repr]

theorem S.casesOn'_eq2 motive empty node cs :
    S.casesOn' motive empty node (S.node cs) = node cs := by
  unfold S.casesOn' S.node
  dsimp only

  -- Got an Eq.mp around the `node` minor premise!
  sorry

-- Ok, let's say we restrict outselves to non-dependent motives in pattern matching.
-- How to define functions?
