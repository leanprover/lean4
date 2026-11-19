import Std.Data.HashSet

structure S' where
  foo : Nat
  bar : Nat

structure S extends S' where
  foobar : Nat
  barfoo : Nat

example : S where   -- No completions expected
               --^ completion

example : S where    -- All field completions expected
                --^ completion

example : S where
    -- All field completions expected
--^ completion

example : S where
  f  -- All field completions matching `f` expected
 --^ completion

example : S where
  foo  -- All field completions matching `foo` expected
   --^ completion

example : S where
  foo :=   -- No completions expected
       --^ completion

example : S where
  foo :=
      -- No completions expected
  --^ completion

example : S where
  foo := 1
      -- All field completions expected
--^ completion

example : S where
  foo := 1;   -- All field completions expected
          --^ completion

example : S := {  } -- All field completions expected
               --^ completion

example : S := {
    -- All field completions expected
--^ completion
}

example : S := {
  f  -- All field completions matching `f` expected
 --^ completion
}

example : S := {
  foo  -- All field completions matching `foo` expected
   --^ completion
}

example : S := {
  foo :=
      -- No completions expected
  --^ completion
}

example : S := {
  foo := 1
    -- All field completions expected
--^ completion
}

example : S :=
  { foo := 1
     } -- All field completions expected
  --^ completion


example : S := { foo := 1,  } -- All field completions expected
                         --^ completion

example (s : S) : S := { s with   } -- All field completions expected
                              --^ completion

example (s : S) : S := { s with   : S } -- All field completions expected
                              --^ completion

example (s : S) : S := { s with f  } -- All field completions matching `f` expected
                               --^ completion

def aLongUniqueIdentifier := 0

example : Std.HashSet Nat := { aLongUniqueIdentifier } -- Identifier completion matching `aLongUniqueIdentifier`
                                                  --^ completion
