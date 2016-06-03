import data.nat

namespace foo
  export nat
  check gcd
end foo

check gcd

namespace foo
  check gcd
end foo

check gcd

namespace bla
   check gcd
   export foo
   check gcd
end bla

section
  open bla
  check gcd
end

check gcd

section
  open foo
  check gcd
end

check gcd

open bla foo nat
print raw gcd
check gcd
