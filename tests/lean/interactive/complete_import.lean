import -- should not trigger
    --^ "command": "complete", "skip_completions": true
import 
     --^ "command": "complete", "skip_completions": true
import .
      --^ "command": "complete", "skip_completions": true
import ..
       --^ "command": "complete", "skip_completions": true
import foo
        --^ "command": "complete", "skip_completions": true
import foo.
         --^ "command": "complete", "skip_completions": true
import .foo
         --^ "command": "complete", "skip_completions": true
import foo 
         --^ "command": "complete", "skip_completions": true
import foo bar
            --^ "command": "complete", "skip_completions": true
