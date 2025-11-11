import Lean.Data.Fmt.Basic
import Lean.Data.Json

open Lean.Fmt

def n := 1000 --0

def hConcat (ds : List Doc) : Doc :=
  match ds with
  | [] => .failure
  | [d] => d
  | d :: ds =>
    ds.foldl (init := d) fun acc d => (Doc.flatten acc).concat d

#eval hConcat [.text "a", .text "b", .text "c"]

def encloseSep (left right sep : Doc) (ds : List Doc) : Doc :=
  match ds with
  | [] => .concat left (.align right)
  | [d] => .join #[left, .align d, .align right]
  | d :: ds =>
    .concat
      (.either )
      (.align right)

def quadratic (n : Nat) : Doc :=
  if n = 0 then
    .text "line"
  else
    .maybeFlattened
      (Doc.joinUsing .nl #[quadratic (n - 1), .text "line"])

def doc := quadratic n

@[noinline]
def format : IO (Option String) := do
  return format? doc 80 100

def bench : IO Unit := do
  discard <| timeit "" format

--#eval bench

-- [x, y, z]
-- a.concat (align b)
-- x.concat (align y) |>.concat (align z)

-- (flatten a).concat b
-- flatten ((flatten x).concat y) |>.concat z
