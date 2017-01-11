import init.meta.attribute
         --^ "command": "info"

@[reducible]
   --^ "command": "info"
def f := tt
       --^ "command": "info"

set_option trace.simplify true
               --^ "command": "info"

example := [tt]
            --^ "command": "info"

example := [tt]++[]
             --^ "command": "info"
