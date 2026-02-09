import Lean open Lean

syntax "👉" (ident <|> "_") : term
#check fun x => `(👉 $x)
#eval match Unhygienic.run `(👉 _) with
  | `(👉 $_:ident) => false
  | `(👉 _) => true
  | _ => false
#eval match Unhygienic.run `(👉 x) with
  | `(👉 _) => false
  | `(👉 $_:ident) => true
  | _ => false

syntax "bar" (&"baz" <|> &"boing") : term
#check fun x => `(bar $x)
#eval match Unhygienic.run `(bar boing) with
  | `(bar baz) => false
  | `(bar boing) => true
  | _ => false
#eval match Unhygienic.run `(bar baz) with
  | `(bar boing) => false
  | `(bar baz) => true
  | _ => false
