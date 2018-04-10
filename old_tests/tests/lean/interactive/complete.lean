prelude

inductive foo

example := foo
           --^ "command": "complete"

-- should not complete empty declaration completion
example := foo
         --^ "command": "complete"

@[reducible]
--^ "command": "complete", "skip_completions": true
example := foo

set_option trace.simplify true
         --^ "command": "complete", "skip_completions": true

#print foo
      --^ "command": "complete", "skip_completions": true

section foo
end foo
  --^ "command": "complete", "skip_completions": true
