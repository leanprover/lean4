section
variable (p : Prop)
def p := 10 -- Error
#check p

namespace Foo
def p := true -- Error
#check p
end Foo
end

def p := 10
#check p
