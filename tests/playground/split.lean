def mkBig : Nat → String → String
| 0 s     := s
| (k+1) s := mkBig k (s ++ "this is a big string\n")

def main : IO Unit :=
let s := mkBig 500000 "" in
let ss := s.split "\n" in
IO.println ss.length *>
IO.println (repr $ "aaa bbb ccc ddd".split) *>
IO.println (repr $ "aaa, bbb, ccc, ddd".split ", ") *>
IO.println (repr $ "aaa, bbb, ccc, ddd".split ",") *>
IO.println (repr $ "aaa,,,bbb,ccc,,ddd".split ",") *>
IO.println (repr $ "aaa#bbb#ccc#ddd".split "#") *>
IO.println (repr $ "aaa#bbb#ccc#ddd".split "") *>
IO.println (repr $ "aaa##bbb".split "##") *>
IO.println (repr $ "aaa##".split "##") *>
IO.println (repr $ "aaa#".split "#") *>
IO.println (repr $ "aaa".split "#") *>
IO.println (repr $ "aaa##bbb##".split "##") *>
IO.println (repr $ "aaa##bbb".split "##")
