namespace Foo
namespace LongNamespaceExample

def x := 10

#check LongNam
            --^ completion
end LongNamespaceExample

#check LongNam
            --^ completion
end Foo

#check Foo.
         --^ completion

#check Foo.LongN
              --^ completion
open Foo

#check LongNam
            --^ completion
