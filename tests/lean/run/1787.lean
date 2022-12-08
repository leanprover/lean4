open Function

def Set (α : Type u) := α → Prop

example {α : Type u}
  (f : α → Type (max u v))
  (U : α) (hU : f U = Set (Sigma f)) :
    let g : Set (Sigma f) → Sigma f := fun (s : Set (Sigma f)) => ⟨U, cast hU.symm s⟩
    ∀ ⦃s t : Set (Sigma f)⦄,
        g s = g t → cast hU (g s).snd = cast hU (g t).snd :=
by
  intros g s t h
  congr -- reduces to `(g s).snd = (g t).snd`, not `g s = g t`
