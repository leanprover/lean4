import Std.Net.Addr

open Std.Net

#eval (IPV4Addr.ofParts 192 168 178 120).toString == "192.168.178.120"
#eval (IPV4Addr.ofParts 1 2 3 4).toString == "1.2.3.4"
#eval (IPV6Addr.ofParts 0xdead 0xbeef 0 0 0 0 0 0).toString == "dead:beef::"
#eval (IPV6Addr.ofParts 0x1234 0x5678 0x9abc 0xdef1 0x4321 0x8765 0xcba9 0x1fed).toString == "1234:5678:9abc:def1:4321:8765:cba9:1fed"

#exit

#eval IPV4Addr.ofString "192.168.178.120" == some (IPV4Addr.ofParts 192 168 178 120)
#eval IPV4Addr.ofString "1.2.3.4" == some (IPV4Addr.ofParts 1 2 3 4)
#eval IPV4Addr.ofString "192.168.300.120" |>.isNone
#eval IPV6Addr.ofString "dead:beef::" == some (IPV6Addr.ofParts 0xdead 0xbeef 0 0 0 0 0 0)
#eval IPV6Addr.ofString "1234:5678:9abc:def1:4321:8765:cba9:1fed" == some (IPV6Addr.ofParts 0x1234 0x5678 0x9abc 0xdef1 0x4321 0x8765 0xcba9 0x1fed)
#eval IPV6Addr.ofString "dead:beef::badaddress" |>.isNone
