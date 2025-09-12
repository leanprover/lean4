inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq, ReflBEq

/-- info: theorem instReflBEqL.{u_1} : ∀ {α : Type u_1} [inst : BEq α] [ReflBEq α], ReflBEq (L α) -/
#guard_msgs in
#print sig instReflBEqL

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : ∀ {n}, α → Vec α n → Vec α (n+1)
deriving BEq, ReflBEq

/--
info: theorem instReflBEqVec.{u_1} : ∀ {α : Type u_1} {a : Nat} [inst : BEq α] [ReflBEq α], ReflBEq (Vec α a)
-/
#guard_msgs in
#print sig instReflBEqVec


inductive Enum
  | mk1 | mk2 | mk3
deriving BEq, ReflBEq

/-- info: theorem instReflBEqEnum : ReflBEq Enum -/
#guard_msgs in
#print sig instReflBEqEnum

-- The following type has `Eq.rec`’s in its `BEq` implementation,
-- but `simp` seems to handle that just fine

inductive WithHEq where
  | mk : ∀ n, Fin n → WithHEq
deriving BEq, ReflBEq

/--
info: instBEqWithHEq.beq_spec (x✝ x✝¹ : WithHEq) :
  (x✝ == x✝¹) =
    if h : (x✝.1 == x✝¹.1) = true then
      Eq.rec (motive := fun a t => x✝¹.1 = a → ⋯ ≍ t → Bool)
        (fun h_1 =>
          Eq.rec (motive := fun x x_1 => Fin x → (x✝.1 == x) = true → (x_2 : x✝.1 = x) → x_2 ≍ ⋯ → Bool)
            (fun b h x h => x✝.2 == b) ⋯ x✝¹.2 ⋯ ⋯)
        ⋯ ⋯ ⋯
    else false
-/
#guard_msgs in
#check instBEqWithHEq.beq_spec

/-- info: instReflBEqWithHEq : ReflBEq WithHEq -/
#guard_msgs in
#check instReflBEqWithHEq

-- No `BEq` derived? Not a great error message yet.

/--
error: failed to synthesize
  BEq Foo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: Tactic `constructor` failed: target is not an inductive datatype

⊢ sorry
-/
#guard_msgs in
structure Foo where
  deriving ReflBEq

/--
@ +5:16...23
error: The `induction` tactic does not support the type `Tree` because it is mutually inductive

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs (positions := true) in
mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving BEq, ReflBEq

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving BEq
end
