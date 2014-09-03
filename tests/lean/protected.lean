import logic

namespace foo
  definition C [protected] := true
  definition D := true
end foo

using foo
check C
check D
