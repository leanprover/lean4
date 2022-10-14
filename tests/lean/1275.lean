import Lean open Lean

syntax "👉" (ident <|> "_") : term
#check `(👉 $_)
#eval match Unhygienic.run `(👉 _) with
  | `(👉 $_:ident) => false
  | `(👉 _) => true
  | _ => false
#eval match Unhygienic.run `(👉 x) with
  | `(👉 _) => false
  | `(👉 $_:ident) => true
  | _ => false
