import Lean.Elab.Command

open Lean Elab Command

declare_syntax_cat myKeyword
syntax "foo" : myKeyword

elab (docComment)? myKeyword ident : command => pure ()

foo hello
