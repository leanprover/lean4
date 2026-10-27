/-!
`isExclusiveUnsafe` returns `false` for values represented as tagged scalars, such as a small `Nat`,
a `Bool`, `()` or `none`, which are not heap objects, instead of reading a reference count through
them (#15677).
-/

unsafe def main (args : List String) : IO Unit := do
  IO.println s!"small Nat: {isExclusiveUnsafe (args.length + 5)}"
  IO.println s!"Bool: {isExclusiveUnsafe args.isEmpty}"
  IO.println s!"Unit: {isExclusiveUnsafe ()}"
  IO.println s!"Option.none: {isExclusiveUnsafe (none : Option Nat)}"
