structure Foo where
  foo : Nat

example (f : Foo) : f
                   --^ insert: .
                    --^ textDocument/completion
