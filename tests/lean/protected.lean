import logic

namespace foo
  definition C [protected] := true
  definition D := true
end foo

open foo
check C
check D
