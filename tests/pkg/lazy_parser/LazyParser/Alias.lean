import Lean

/-!
Registers a parser alias in a non-builtin initializer, as Mathlib does for `superscript`. The alias
is registered only when the module is imported, after the environment's extension states have
been created.
-/

open Lean Parser

@[run_parser_attribute_hooks] def bangTok : Parser := symbol "bang!"

initialize register_parser_alias bangTok
