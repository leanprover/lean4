import logic

namespace foo
   definition t := true
end foo
open foo

namespace bla
  definition t := false
  check foo.t   -- <<< must print foo.t : Prop instead of t : Prop
end bla
