import Lean.Elab.Frontend

open Lean Elab in
#eval show IO _ from do
  discard <| importModules #[Name.anonymous] {} 0
