--

variable p : Prop
definition foo (q : Prop) : q → true :=
begin
  intro r,
  apply true.intro
end
