namespace Foo
namespace LongNamespaceExample

def x := 10

#check LongName
             --^ completion
end LongNamespaceExample

#check LongName
             --^ completion
end Foo

#check Foo.
         --^ completion

#check Foo.LongN
              --^ completion
open Foo

#check LongName
             --^ completion
