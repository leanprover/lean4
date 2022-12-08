import Lean
open Lean PrettyPrinter

def fmt (stx : CoreM Syntax) : CoreM Format := stx >>= formatTerm

#eval fmt `(if c then do t else e)
#eval fmt `(if c then do t; t else e)
#eval fmt `(if c then do t else do e)
#eval fmt `(if let x := c then do t else do e)
#eval fmt `(if c then do t else if c then do t else do e) -- FIXME: make this cascade better?
#eval fmt `(do if c then t else e)
#eval fmt `(do if c then t else if c then t else e)

#eval fmt `(def foo := by
  · skip; skip
  · skip; skip
    skip
    (skip; skip)
    (skip; skip
     try skip; skip
     try skip
         skip
     skip))

#eval fmt `(by
  try
  skip
  skip)

set_option format.indent 3 in
#eval fmt `(by
  try
  skip
  skip)
set_option format.indent 4 in
#eval fmt `(by
  try
  skip
  skip)
set_option format.indent 4 in
#eval fmt `(by
  try
    skip
    skip
  skip)

#eval fmt `({
  foo := bar
  bar := foo + bar
})

#eval fmt `(let x := { foo := bar
                       bar := foo + bar }
            x)
