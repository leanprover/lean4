open nat

namespace bla
  local abbreviation foo : nat := 10 + 1
  definition tst : nat := foo
  print definition tst
end bla

-- abbreviation is gone
print definition bla.tst

check bla.foo
open bla
check foo

print definition tst

namespace bla2
  abbreviation foo2 : nat := 1
  definition tst2 : nat := foo2
  print definition tst2
end bla2

print definition bla2.tst2
open bla2
print definition bla2.tst2
print definition tst2
