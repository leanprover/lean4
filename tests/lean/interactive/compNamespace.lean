namespace Foo
namespace LongNamespaceExample

def x := 10

#check LongNam
            --^ textDocument/completion
end LongNamespaceExample

#check LongNam
            --^ textDocument/completion
end Foo

#check Foo.
         --^ textDocument/completion

#check Foo.LongN
              --^ textDocument/completion
open Foo

#check LongNam
            --^ textDocument/completion
