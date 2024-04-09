private structure Foo where
  x : Nat

def foobar (f : Foo) := f.
                        --^ textDocument/completion
