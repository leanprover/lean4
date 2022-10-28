import Lean
open Lean

def fmt (stx : CoreM Syntax) : CoreM Format := stx >>= PrettyPrinter.formatTerm

#eval fmt `(if c then do t else e)
#eval fmt `(if c then do t; t else e)
#eval fmt `(if c then do t else do e)
#eval fmt `(if let x := c then do t else do e)
#eval fmt `(if c then do t else if c then do t else do e) -- FIXME: make this cascade better?
#eval fmt `(do if c then t else e)
#eval fmt `(do if c then t else if c then t else e)
