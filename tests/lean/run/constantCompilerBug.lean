import Init.Lean

new_frontend

open Lean
open Lean.Parser

def regBlaParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute (mkNameSimple "blaParser") (mkNameSimple "bla")

@[inline] def parser : Parser :=
categoryParser (mkNameSimple "bla") 0

#check @parser
