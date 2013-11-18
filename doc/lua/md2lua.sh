#!/usr/bin/awk -f
BEGIN{ in_block = 0 }
!/```/{ if (in_block == 1) print $0; else print "" }
/```/{ in_block = 0; print "" }
/```lua/{ in_block = 1; print "" }
