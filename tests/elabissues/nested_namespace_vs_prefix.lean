/-
@rwbarton found the following surprising:
-/

-- 1. When you are in `A.B`, you are not in `A`.

def A.foo : String := "A.foo"

namespace A.B

def bar : String := foo -- error: unknown identifier 'foo'

end A.B

namespace A
namespace B

def bar : String := foo -- succeeds

end B
end A

/-
I (@dselsam) agree it is a little weird, and suggest
either we disallow the first case or we make it sugar for the second.
-/
