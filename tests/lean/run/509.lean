class has_note (M : Type) where
  note : M

notation "♩" => has_note.note

class has_note2 (M : Type) extends has_note M

variable {ι : Type} (β : ι → Type)

structure foo [∀ i, has_note (β i)] : Type where
  to_fun : ∀ i, β i

instance foo.has_note [∀ i, has_note (β i)] : has_note (foo (λ i => β i)) where
  note := { to_fun := λ _ => ♩ }

instance foo.has_note2 [∀ i, has_note2 (β i)] : has_note2 (foo (λ i => β i)) where
  note := ♩

variable (α : Type) (M : Type)

structure bar [has_note M] where
  to_fun : α → M

instance bar.has_note [has_note M] : has_note (bar α M) where
  note := { to_fun := λ _ => ♩ }

instance bar.has_note2 [has_note2 M] : has_note2 (bar α M) where
  note := ♩

example [has_note2 M] : has_note2 (foo (λ (i : ι) => bar (β i) M)) :=
inferInstance

example [has_note2 M] : has_note2 (foo (λ (i : ι) => bar (β i) M)) :=
foo.has_note2 _
