lemma ex {α : id Type} [has_add α] : true :=
begin
  dsimp at α -- should fail because the frozen instance `[has_add α]` depends on `α`
end
