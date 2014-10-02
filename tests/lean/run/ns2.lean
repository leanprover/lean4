definition foo.id {A : Type} (a : A) := a
constant foo.T : Type.{1}
check foo.id
check foo.T

inductive foo.v.I := unit : foo.v.I

check foo.v.I
check foo.v.I.unit

namespace foo
  check id
  check T
  check v.I
end foo

namespace bla
  definition vvv.pr {A : Type} (a b : A) := a
  check vvv.pr
end bla
check bla.vvv.pr

namespace bla
namespace vvv
  check pr
  inductive my.empty : Type
end vvv
end bla
check bla.vvv.my.empty
