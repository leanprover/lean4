import Lean

open Lean

initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

register_simp_attr my_simp "my own simp attribute"
