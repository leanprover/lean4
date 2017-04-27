-- Companion file for the abstract_ns test.

namespace ns2

def foo : fin 7 := ⟨3, dec_trivial⟩
def foo' : fin 7 := ⟨3, by abstract {exact dec_trivial}⟩

end ns2
