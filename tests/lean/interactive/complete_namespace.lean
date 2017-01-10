prelude

inductive foo.bar

open foo
   --^ "command": "complete"

namespace foo
  open bar
     --^ "command": "complete"
end foo
