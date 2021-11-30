structure Bar where
        --^ textDocument/references : {"context": {"includeDeclaration": true}}
        --^ textDocument/references : {"context": {"includeDeclaration": false}}

structure Foo where
        --^ textDocument/references : {"context": {"includeDeclaration": true}}
        --^ textDocument/references : {"context": {"includeDeclaration": false}}
  a : Nat
--^ textDocument/references : {"context": {"includeDeclaration": true}}
--^ textDocument/references : {"context": {"includeDeclaration": false}}
    --^ textDocument/references : {"context": {"includeDeclaration": true}}
  b : Bar
--^ textDocument/references : {"context": {"includeDeclaration": true}}
--^ textDocument/references : {"context": {"includeDeclaration": false}}
    --^ textDocument/references : {"context": {"includeDeclaration": true}}
    --^ textDocument/references : {"context": {"includeDeclaration": false}}

def mkFoo : Foo := {
  a := 2
  b := ⟨⟩
: Foo }

def foo (x : Foo) : Nat :=
  --^ textDocument/references : {"context": {"includeDeclaration": true}}
  --^ textDocument/references : {"context": {"includeDeclaration": false}}
       --^ textDocument/references : {"context": {"includeDeclaration": true}}
       --^ textDocument/references : {"context": {"includeDeclaration": false}}
  let x := x.a
         --^ textDocument/references : {"context": {"includeDeclaration": true}}
         --^ textDocument/references : {"context": {"includeDeclaration": false}}
    --^ textDocument/references : {"context": {"includeDeclaration": true}}
    --^ textDocument/references : {"context": {"includeDeclaration": false}}
  x
--^ textDocument/references : {"context": {"includeDeclaration": true}}
--^ textDocument/references : {"context": {"includeDeclaration": false}}
