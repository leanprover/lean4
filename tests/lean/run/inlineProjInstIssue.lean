class NameableType (τ : Type) where
  name : String

instance : NameableType String where
  name := "String"

instance [inst : NameableType α] : NameableType (Array α) where
  name :=
    if inst.name.contains ' ' then
      s!"Array ({inst.name})"
    else
      s!"Array {inst.name}"

def foo : String :=
  NameableType.name (Array String)
