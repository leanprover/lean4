namespace bla
section
  private definition foo : inhabited Prop :=
  inhabited.mk false

  instance [priority 1000] foo

  example : inhabited.default Prop = false :=
  rfl
end
end bla
