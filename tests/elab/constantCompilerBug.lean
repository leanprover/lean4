import Lean



open Lean
open Lean.Parser

def regBlaParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute (Name.mkSimple "bla_parser") (Name.mkSimple "bla")

@[inline] def parser : Parser :=
categoryParser (Name.mkSimple "bla") 0

#check @parser
