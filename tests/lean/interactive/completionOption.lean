
set_option format
               --^ textDocument/completion

set_option format.in
                  --^ textDocument/completion

set_option trace.pp.ana
                     --^ textDocument/completion

set_option trace.pp.analyze
                         --^ textDocument/completion

set_option format true
               --^ textDocument/completion

set_option format.
                --^ textDocument/completion

#check false -- curiously completion with a trailing dot worked even before special casing if triggered on the last token
