import logic

namespace foo
  protected definition C := true
  definition D := true
end foo

open foo
check foo.C
check D
