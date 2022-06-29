import Lean
open Lean Elab

#eval show TermElabM _ from do
  let x := mkIdent `x
  let xs := #[x,x,x,x]
  let ys := xs
  PrettyPrinter.ppTerm <|<-
    `(frobnicate { $[$xs:ident := $ys:term],* })

#eval show TermElabM _ from do
  let x := mkIdent `x
  let xs := #[x,x,x,x]
  let ys := xs
  PrettyPrinter.ppTerm <|<-
    `(frobnicate { $[$xs:ident := $ys:term]* })
