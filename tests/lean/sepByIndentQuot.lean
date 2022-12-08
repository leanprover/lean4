import Lean
open Lean Elab

#eval do
  let x := mkIdent `x
  let xs := #[x,x,x,x]
  let ys := xs
  PrettyPrinter.ppTerm <|<-
    `(frobnicate { $[$xs:ident := $ys:term],* })

#eval do
  let x := mkIdent `x
  let xs := #[x,x,x,x]
  let ys := xs
  PrettyPrinter.ppTerm <|<-
    `(frobnicate { $[$xs:ident := $ys:term]* })
