open tactic

open lean.parser
open interactive
open interactive.types

meta def fooo (p : parse $ optional $ pexpr_list_or_texpr) : tactic unit := skip
run_cmd add_interactive [`fooo]

example : false :=
begin
  fooo,
   --^ "command": "info"
  fooo ,
    --^ "command": "info"
  fooo [ ],
      --^ "command": "info"
  fooo [d] ,
        --^ "command": "info"
  _root_.fooo none
--^ "command": "info"
end
