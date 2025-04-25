import Std.Data.HashMap

def foo := include_str "inputs" / "foo.txt"
def bar := include_str "inputs" / "barz" / "bar.txt"
def baz := include_str "inputs" / "barz" / "baz.txt"
def untraced := include_str "inputs" / "untraced.txt"
def untracedBarz := include_str "inputs" / "barz" / "untraced.txt"

def inputs : Std.HashMap String String :=
  (∅ : Std.HashMap ..)
  |>.insert "foo" foo
  |>.insert "bar" bar
  |>.insert "baz" baz
  |>.insert "untraced" untraced
  |>.insert "untracedBarz" untracedBarz

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.print foo
    IO.print bar
    IO.print baz
    IO.print untraced
    IO.print untracedBarz
  else
    let input :: [] := args
      | throw <| .userError "USAGE: lake exe test [input]"
    let some value := inputs[input]?
      | throw <| .userError s!"error: unknown input '{input}'"
    IO.print value
