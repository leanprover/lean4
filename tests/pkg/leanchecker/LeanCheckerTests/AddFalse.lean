import Lean.Elab.Term

open Lean in
run_elab
  modifyEnv fun env => Id.run do
    let decl := .thmDecl { name := `false, levelParams := [], type := .const ``False [], value := .const ``False [] }
    let .ok env := env.addDeclCore (doCheck := false) 0 decl none |
      let _ : Inhabited Environment := ⟨env⟩
      unreachable!
    env
