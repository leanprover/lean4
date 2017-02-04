example (p q : Prop) : p → q → p :=
begin
  trace "foo",
  intros,
  trace "hello world",
  assumption
end
