structure Foo where
  foo : Nat

example (f : Foo) : f.
                    --^ completion
example (f : Foo) : f.f
                     --^ completion
example (f : Foo) : id f |>.
                          --^ completion
example (f : Foo) : id f |>.f
                           --^ completion
