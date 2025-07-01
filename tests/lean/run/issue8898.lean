/-! # Preliminary -/

/--
`PoisonOr` is a simple wrapper around `Option`
-/
structure PoisonOr (α : Type) where
  toOption : Option α

namespace PoisonOr

def value : α → PoisonOr α := (⟨some ·⟩)

instance : Bind PoisonOr where
  bind := fun a f => match a with
    | ⟨none⟩    => ⟨none⟩
    | ⟨some a⟩  => f a

theorem bind_assoc (x : PoisonOr α) (f : α → PoisonOr β) (g : β → PoisonOr γ) :
    x >>= f >>= g = x >>= fun x => f x >>= g := by
  rcases x with (_|_) <;> rfl

end PoisonOr

/-! # MWE -/

def BitVec.umulOverflow' {w : Nat} (x y : BitVec w) : Prop :=
  x.toNat * y.toNat ≥ 0
  -- -----^
  -- Making this `+` has no effect, the error remains.
  --
  -- However, replacing `x.toNat` with a constant (even if large), does make the
  --   error disappear
  --
  -- Also note that the rhs was originally `2 ^ w`, but I've replaced it with
  -- `0` to rule out `2 ^ w` being computed. This had no effect on the error.

instance : DecidableRel (@BitVec.umulOverflow' w) := by
  unfold BitVec.umulOverflow';
  -- If we `sorry` out this instance, the error disappears
  -- sorry
  infer_instance


/-
The following gives the error:

  (kernel) deep recursion detected

-/
theorem mwe (x' : BitVec 32) :
    (do
      let _z ←
        (do
          let y' ← PoisonOr.value 0#32
          -- ----- ^^^^^^^^^^^^^^
          -- Replacing the `PoisonOr` wrapper with `Option` (in the whole MWE)
          -- makes the error disappear
          --
          if x'.umulOverflow' (65537#_) then
          -- ----------------- ^^^^^^^
          -- Making this constant smaller, or replacing it with a variable,
          -- makes the error disappear
          --
            PoisonOr.value 0#32
          else
            PoisonOr.value 0#32)
      PoisonOr.value 0) = PoisonOr.value 0 := by
  -- Running `simp only [ite_self]` first makes the error disappear
  --   (but is not applicable in my actual scenario, as the branches of the real
  --    code aren't the same)
  -- Similarly, rewriting the statement to not have the if-then-else also
  -- makes the error disappear, even if the if condition is still present.

  rw [PoisonOr.bind_assoc]
  -- ^^ This rewrite is what seems to trigger the recursion, removing it
  --    makes the error disappear.
  sorry
