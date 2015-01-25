namespace bla
section
  private definition foo : inhabited Prop :=
  inhabited.mk false

  attribute foo [instance] [priority 1000]

  example : default Prop = false :=
  rfl
end
end bla
