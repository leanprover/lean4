
set_option format
               --^ completion

set_option format.in
                  --^ completion

set_option trace.pp.ana
                     --^ completion

set_option trace.pp.analyze
                         --^ completion

set_option format true
               --^ completion

set_option format.
                --^ completion

#check false -- curiously completion with a trailing dot worked even before special casing if triggered on the last token
