scope
   using Nat
   print add 0 1
   check add_assoc
end

print add 0 1

namespace foo
    using Nat
    print add 0 1
end

using Nat::add plus
check plus_assoc

print add 0 1
