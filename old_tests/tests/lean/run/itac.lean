axiom addz {A : Type} [has_add A] [has_zero A] : ∀ a : A, a + 0 = a

example {A : Type} [has_add A] [has_zero A] (a b c : A) : (a + 0) + (b + 0) + (c + 0) = a + b + c :=
begin
  repeat {rw addz}
end

example {A : Type} [has_add A] [has_zero A] (a b c : A) : (a + 0) + (b + 0) + (c + 0) = a + b + c :=
begin
  repeat {rw addz, trace "------", trace_state}
end
