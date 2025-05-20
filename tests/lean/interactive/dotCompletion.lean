namespace Outer

def hi : Nat := 42

namespace Inner

end Inner

end Outer

#print Outer.
           --^ textDocument/completion

syntax Outer. := "hi"
           --^ textDocument/completion

syntax "test_me " Outer.stx : command


-- TODO: don't suggest `hi`
namespace Outer.
              --^ textDocument/completion
