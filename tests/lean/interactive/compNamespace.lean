namespace Foo
namespace LongNamespaceExample

def x := 10

#check LongN
          --^ textDocument/completion
end LongNamespaceExample

#check LongN
          --^ textDocument/completion
end Foo

#check Foo.
         --^ textDocument/completion

#check Foo.LongN
              --^ textDocument/completion
open Foo

#check LongN
          --^ textDocument/completion
