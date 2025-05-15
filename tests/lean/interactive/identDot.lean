macro "#test " i:identDot : command => `(#print $i)

namespace MyNamespace

def foo : Nat := 33

end MyNamespace

#test MyNamespace.
                --^ textDocument/completion
