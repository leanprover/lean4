module

public meta import Lean.Parser.Module.Syntax
public meta import Lean.Elab.Command

/-! Checks that `all` is nonreserved in `Lean.Parser.Module.import` and can
therefore be used as an identifier even if `Lean.Parser.Module.import` appears
in a `syntax` command (which reserves all symbols in the syntax). -/

syntax (name := fooCmd) "#foo " Lean.Parser.Module.import : command

def all := 3

def foo := all

open Lean

elab_rules : command
| `(fooCmd| #foo $[public]? $[meta]? import $[all%$tk]? $_:ident) => logInfo m!"all: {tk.isSome}"

/-- info: all: false -/
#guard_msgs in
#foo import x

/-- info: all: false -/
#guard_msgs in
#foo public import x

/-- info: all: true -/
#guard_msgs in
#foo import all x

/-- info: all: true -/
#guard_msgs in
#foo import all all
