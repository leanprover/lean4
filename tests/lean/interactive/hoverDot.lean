structure Foo where
  f₁ : Nat

def Foo.f₂ (f : Foo) : Nat :=
  f.f₁

def Foo.foo : Foo := ⟨10⟩

#check Foo.foo.f₁.succ
         --^ textDocument/hover

open Foo
#check foo.f₁.succ
         --^ textDocument/hover
            --^ textDocument/hover
#check foo.f₂.succ
         --^ textDocument/hover
            --^ textDocument/hover
#check (foo).f₂.succ
           --^ textDocument/hover
              --^ textDocument/hover
#check foo |>.f₂.succ
            --^ textDocument/hover
               --^ textDocument/hover
