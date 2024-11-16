abbrev T.{u} : Unit := (fun (_ : Sort u) => ()) PUnit.{u}

set_option pp.universes true
def test.{u, v} : T.{u} = T.{v} := rfl
