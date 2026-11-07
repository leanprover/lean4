/-!
Mathlib-free version of `y_surjective` in `Mathlib/Condensed/Light/Sequence.lean`.

The last `grind` call needs the funext case split `F = F'` for the two `Subtype.mk` arguments `F`
(from the goal) and `F'` (from the `y_apply` instance), which differ only inside nested proofs.
When the proposition `S' π F'` is asserted before the instance is internalized, `F'` is first seen
as an argument of `S'`. Funext split candidates were only recorded for the first parent of a
lambda, so the candidate for the `Subtype.mk` arguments was never created and the proof failed.
-/

variable {S T O : Type}

def S' (π : T → S × O) (x : ∀ o : O, {t // (π t).2 = o}) : Prop :=
  ∀ n m, (π (x n).val).1 = (π (x m).val).1

@[grind =]
theorem S'_iff (π : T → S × O) (x : ∀ o : O, {t // (π t).2 = o}) :
    S' π x ↔ ∀ n m, (π (x n).val).1 = (π (x m).val).1 :=
  Iff.rfl

def y (π : T → S × O) (o₀ : O) : {x // S' π x} → S := fun x ↦ (π (x.val o₀).val).1

@[grind =]
theorem y_apply (π : T → S × O) (o₀ : O) (x : {x // S' π x}) :
    y π o₀ x = (π (x.val o₀).val).1 := rfl

theorem y_surjective (π : T → S × O) (o₀ : O) (hπ : Function.Surjective π) :
    Function.Surjective (y π o₀) := by
  intro s
  let p (s : S) (n : O) : T := (hπ (s, n)).choose
  have hp (s : S) (n : O) : π (p s n) = (s, n) := (hπ (s, n)).choose_spec
  exact ⟨⟨fun n ↦ ⟨p s n, by grind⟩, by grind⟩, by grind⟩
