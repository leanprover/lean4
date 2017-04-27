-- Companion file for the abstract_ns test.

namespace ns1

def foo : fin 7 := ⟨3, dec_trivial⟩
def foo' : fin 7 := ⟨3, by abstract {exact dec_trivial}⟩

end ns1
