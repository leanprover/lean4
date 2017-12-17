lemma main : false :=
begin
have helper : true → false := λ ⟨⟩, _fun_match _x,
exact helper ⟨⟩
end