namespace Ex0

-- NB: no parameter
theorem elim_without_param {motive : Nat → Prop} (case1 : ∀ n, motive n) (n : Nat)  : motive n :=
  case1 _

example (n : Nat) : n = n := by
  induction n using elim_without_param
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using @elim_without_param
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using (elim_without_param) -- Error: unexpected eliminator resulting type
  case case1 n => rfl

end Ex0

namespace Ex1

-- NB: p before motive
theorem elim_with_param (p : Bool) {motive : Nat → Prop} (case1 : ∀ n, motive n) (n : Nat)  : motive n :=
  if p then case1 _ else case1 _

example (n : Nat) : n = n := by
  induction n using elim_with_param
  case p => exact true -- uninstantiated parameters becomes goal
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using @elim_with_param
  case p => exact true -- uninstantiated parameters becomes goal
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using elim_with_param (p := true)
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using elim_with_param true
  case case1 n => rfl

example (n : Nat) : n = n := by
  -- not really a useful idiom, but it better works:
  induction n using fun motive case1 n => @elim_with_param true motive case1 n
  case case1 n => rfl

example (n : Nat) : n = n := by
  -- NB: no renaming of cases this way?
  induction n using fun motive the_case n => @elim_with_param true motive the_case n
  case case1 n => rfl

end Ex1

namespace Ex2

-- NB: p after motive
theorem elim_with_param {motive : Nat → Prop} (case1 : ∀ n, motive n) (n : Nat) (p : Bool) : motive n :=
  if p then case1 _ else case1 _

example (n : Nat) : n = n := by
  induction n using elim_with_param
  case p => exact true
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using @elim_with_param
  case p => exact true
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using elim_with_param (p := true)
  case case1 n => rfl

example (n : Nat) : n = n := by
  induction n using @elim_with_param (p := true)
  case case1 n => rfl

example (n : Nat) : n = n := by
  -- This renames the cases with unhelpful names
  induction n using elim_with_param _ _ true
  case x_1 n => rfl

example (n : Nat) : n = n := by
  -- We can put in custom names
  induction n using elim_with_param ?case2 _ true
  case case2 n => rfl

example (n : Nat) : n = n := by
  -- not really a useful idiom, but it works:
  induction n using fun motive case1 n => @elim_with_param motive case1 n true
  case case1 n => rfl

end Ex2

namespace Ex3

-- Mutual induction, multiple motives

mutual
inductive A : Type u where | mkA : B → A | A : A
inductive B : Type u where | mkB : A → B
end

-- NB: A.rec is configured as elab_as_elim,
-- but in `using` it should not matter

-- For comparison, a copy without that attribute
noncomputable def A_rec := @A.rec

set_option linter.unusedVariables false

example (a : A) : True := by
  -- motive_2 becomes a mvar
  induction a using A.rec
  case mkA b IH =>
    refine True.rec ?_ IH -- A hack to instantiate the motive_2 mvar
    exact trivial
  case A => exact trivial
  case mkB b IH => show True; exact trivial

example (a : A) : True := by
  -- motive_2 becomes a mvar
  induction a using A_rec
  case mkA b IH =>
    refine True.rec ?_ IH -- A hack to instantiate the motive_2 mvar
    exact trivial
  case A => exact trivial
  case mkB b IH => show True; exact trivial -- Error: type mismatch

example (a : A) : True := by
  -- motive_2 becomes a mvar
  induction a using @A.rec
  case mkA b IH =>
    refine True.rec ?_ IH -- A hack to instantiate the motive_2 mvar
    exact trivial
  case A => exact trivial
  case mkB b IH => show True; exact trivial

example (a : A) : True := by
  -- motive_2 becomes a mvar
  induction a using @A_rec
  case mkA b IH =>
    refine True.rec ?_ IH -- A hack to instantiate the motive_2 mvar
    exact trivial
  case A => exact trivial
  case mkB b IH => show True; exact trivial

example (a : A) : True := by
  induction a using fun motive_1 => @A.rec motive_1 (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

example (a : A) : True := by
  induction a using fun motive_1 => @A_rec motive_1 (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

example (a : A) : True := by
  induction a using @A.rec (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

example (a : A) : True := by
  induction a using @A_rec (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

example (a : A) : True := by
  -- A.rec is marked elab_as_elim, and normally elaborating
  -- #check A.rec (motive_2 := fun b => True)
  -- fails with
  -- > failed to elaborate eliminator, expected type is not available
  -- so we elaborate with heedElabAsElim := false
  induction a using A.rec (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

example (a : A) : True := by
  induction a using A_rec (motive_2 := fun b => True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH => exact trivial

end Ex3

namespace Ex4

-- We can use parameters as elaborators

set_option linter.unusedVariables false in
example
  (α : Type u)
  (ela : ∀ {motive : α → Prop} (case1 : ∀ (x : α), motive x) (x : α), motive x)
  (x : α)
  : x = x := by
  induction x using ela
  case case1 x => rfl

end Ex4

namespace Ex5

-- Multiple motives, different number of extra assumptions

mutual
inductive A : Type u where | mkA : B → A | A : A
inductive B : Type u where | mkB : A → B
end

set_option linter.unusedVariables false in
example (a : A) : True := by
  induction a using A.rec (motive_2 := fun b => (heq : b = b) -> True)
  case mkA b IH => exact trivial
  case A => exact trivial
  case mkB b IH h => exact trivial

end Ex5
