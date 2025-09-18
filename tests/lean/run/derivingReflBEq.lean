-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq, LawfulBEq

/-- info: theorem instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α) -/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: theorem instReflBEqVec.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : BEq α] [ReflBEq α], ReflBEq (Vec α a)
-/
#guard_msgs in
#print sig instReflBEqVec


inductive Enum
  | mk1 | mk2 | mk3
deriving BEq, ReflBEq --, LawfulBEq

/--
info: theorem instReflBEqEnum : ReflBEq Enum :=
{ rfl := fun x => BEq.refl x.ctorIdx }
-/
#guard_msgs in #print instReflBEqEnum

/--
info: theorem instLawfulBEqEnum : LawfulBEq Enum :=
{ toReflBEq := instReflBEqEnum,
  eq_of_beq := fun {x} =>
    @Enum.rec (fun {x} => ∀ {b : Enum}, (x == b) = true → x = b)
      (fun {y} =>
        Enum.casesOn (motive := fun t => y = t → (Enum.mk1 == y) = true → Enum.mk1 = y) y
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk1 == y) = true → Enum.mk1 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk1 Enum.mk1))
                    (eq_self Enum.mk1)))
                fun a => True.intro)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk1 == y) = true → Enum.mk1 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk1 Enum.mk2))
                    (Eq.refl (Enum.mk1 = Enum.mk2))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk1 == y) = true → Enum.mk1 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk1 Enum.mk3))
                    (Eq.refl (Enum.mk1 = Enum.mk3))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (Eq.refl y))
      (fun {y} =>
        Enum.casesOn (motive := fun t => y = t → (Enum.mk2 == y) = true → Enum.mk2 = y) y
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk2 == y) = true → Enum.mk2 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk2 Enum.mk1))
                    (Eq.refl (Enum.mk2 = Enum.mk1))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk2 == y) = true → Enum.mk2 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk2 Enum.mk2))
                    (eq_self Enum.mk2)))
                fun a => True.intro)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk2 == y) = true → Enum.mk2 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk2 Enum.mk3))
                    (Eq.refl (Enum.mk2 = Enum.mk3))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (Eq.refl y))
      (fun {y} =>
        Enum.casesOn (motive := fun t => y = t → (Enum.mk3 == y) = true → Enum.mk3 = y) y
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk3 == y) = true → Enum.mk3 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk3 Enum.mk1))
                    (Eq.refl (Enum.mk3 = Enum.mk1))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk3 == y) = true → Enum.mk3 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk3 Enum.mk2))
                    (Eq.refl (Enum.mk3 = Enum.mk2))))
                fun a => Bool.noConfusion a)
              (Eq.symm h))
          (fun h =>
            Eq.ndrec (motive := fun {y} => (Enum.mk3 == y) = true → Enum.mk3 = y)
              (Eq.mpr
                (id
                  (implies_congr (congrArg (fun x => x = true) (instBEqEnum.beq_spec_1 Enum.mk3 Enum.mk3))
                    (eq_self Enum.mk3)))
                fun a => True.intro)
              (Eq.symm h))
          (Eq.refl y))
      x }
-/
#guard_msgs in #print instLawfulBEqEnum

-- The following type has `Eq.rec`’s in its `BEq` implementation,
-- but `simp` seems to handle that just fine

inductive WithHEq (α : Type u) : Nat → Type u where
  | nil  : WithHEq α 0
  | cons : ∀ {n m} , α → WithHEq α n → WithHEq α m → WithHEq α (n+1)
deriving BEq, ReflBEq, LawfulBEq

/--
info: instReflBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [ReflBEq α✝] : ReflBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instReflBEqWithHEq

/--
info: instLawfulBEqWithHEq.{u_1} {α✝ : Type u_1} {a✝ : Nat} [BEq α✝] [LawfulBEq α✝] : LawfulBEq (WithHEq α✝ a✝)
-/
#guard_msgs in
#check instLawfulBEqWithHEq


-- No `BEq` derived? Not a great error message yet, but the error location helps, so good enough.

/--
error: failed to synthesize
  BEq Foo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
structure Foo where
  deriving ReflBEq

-- No `ReflBEq` but `LawfulBEq`? ot a great error message yet.

/--
@ +2:16...25
error: failed to synthesize
  ReflBEq Bar

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (positions := true) in
structure Bar where
  deriving BEq, LawfulBEq

/--
@ +5:16...23
error: Deriving `ReflBEq` for mutual inductives is not supported
-/
#guard_msgs (positions := true) in
mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving BEq, ReflBEq, LawfulBEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end
