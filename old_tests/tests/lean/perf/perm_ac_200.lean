import data.list.perm
open list perm option nat
attribute [reducible]
definition denote {X : Type} (default : X) [add_comm_semigroup X] (xs : list X) : list nat -> X
| nil := default
| (cons i is) := match nth xs i with
                 | none := default
                 | (some x) := match is with
                               | nil := x
                               | _ := x + denote is
                               end
                 end
axiom perm_ac {X : Type} (default : X) [add_comm_semigroup X] (xs : list X) (is js : list nat) :
  perm is js -> denote default xs is = denote default xs js
constants (X : Type.{1}) (X_acsg : add_comm_semigroup X) (X_deceq : decidable_eq X)
attribute X_acsg [instance]
attribute X_deceq [instance]

open tactic expr decidable

meta_definition is_poly_bin_app : expr -> option name
| (app (app (app (app (const op ls) A) s) lhs) rhs) := some op
| _  := none

meta_definition is_add (e : expr) : bool  :=
match is_poly_bin_app e with
| some op := to_bool (op = "add")
| none    := ff
end

meta_definition perm_add (e1 e2 : expr) : tactic expr :=
do when (is_add e1 = ff) (fail "given expression is not an addition"),
   add_fn : expr <- return $ app_fn (app_fn e1),
   A      : expr <- return $ app_arg (app_fn add_fn),
   s1     : expr <- mk_app "add_semigroup" [A] >>= mk_instance,
   assoc  : expr <- mk_mapp ("add" <.> "assoc") [some A, some s1],
   s2     : expr <- mk_app "add_comm_semigroup" [A] >>= mk_instance,
   comm   : expr <- mk_mapp ("add" <.> "comm") [some A, some s2],
   perm_ac add_fn assoc comm e1 e2

meta_definition perm_add_eq : tactic unit :=
do
   (lhs, rhs) <- target >>= match_eq,
   perm_add lhs rhs >>= exact


constants (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100 x101 x102 x103 x104 x105 x106 x107 x108 x109 x110 x111 x112 x113 x114 x115 x116 x117 x118 x119 x120 x121 x122 x123 x124 x125 x126 x127 x128 x129 x130 x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151 x152 x153 x154 x155 x156 x157 x158 x159 x160 x161 x162 x163 x164 x165 x166 x167 x168 x169 x170 x171 x172 x173 x174 x175 x176 x177 x178 x179 x180 x181 x182 x183 x184 x185 x186 x187 x188 x189 x190 x191 x192 x193 x194 x195 x196 x197 x198 x199  : X)
---------
example : x153 + (x27 + (x137 + (x31 + (x155 + (x110 + (x54 + (x145 + (x198 + (x0 + (x102 + (x188 + (x126 + (x35 + (x196 + (x164 + (x9 + (x123 + (x121 + (x171 + (x103 + (x117 + (x129 + (x144 + (x61 + (x84 + (x37 + (x184 + (x94 + (x60 + (x41 + (x70 + (x29 + (x74 + (x148 + (x62 + (x113 + (x157 + (x38 + (x55 + (x2 + (x146 + (x106 + (x182 + (x192 + (x57 + (x174 + (x30 + (x17 + (x91 + (x53 + (x75 + (x36 + (x183 + (x95 + (x79 + (x142 + (x3 + (x52 + (x125 + (x185 + (x47 + (x65 + (x112 + (x50 + (x21 + (x108 + (x7 + (x147 + (x24 + (x140 + (x63 + (x76 + (x150 + (x119 + (x81 + (x152 + (x118 + (x96 + (x4 + (x107 + (x101 + (x172 + (x58 + (x92 + (x135 + (x173 + (x25 + (x158 + (x104 + (x78 + (x12 + (x130 + (x105 + (x44 + (x88 + (x5 + (x131 + (x83 + (x176 + (x49 + (x111 + (x97 + (x132 + (x141 + (x190 + (x51 + (x100 + (x115 + (x189 + (x114 + (x181 + (x15 + (x133 + (x10 + (x149 + (x34 + (x22 + (x72 + (x45 + (x20 + (x32 + (x87 + (x166 + (x163 + (x168 + (x23 + (x90 + (x156 + (x85 + (x116 + (x8 + (x139 + (x71 + (x1 + (x162 + (x77 + (x186 + (x180 + (x109 + (x19 + (x42 + (x80 + (x120 + (x199 + (x56 + (x16 + (x66 + (x48 + (x161 + (x177 + (x195 + (x167 + (x13 + (x33 + (x151 + (x178 + (x39 + (x128 + (x138 + (x127 + (x46 + (x82 + (x134 + (x159 + (x154 + (x194 + (x18 + (x43 + (x136 + (x98 + (x69 + (x73 + (x26 + (x191 + (x124 + (x86 + (x89 + (x165 + (x68 + (x160 + (x67 + (x14 + (x169 + (x170 + (x197 + (x40 + (x193 + (x93 + (x64 + (x122 + (x6 + (x143 + (x179 + (x11 + (x175 + (x99 + (x187 + (x28 + (x59))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = x23 + (x12 + (x190 + (x178 + (x194 + (x186 + (x69 + (x179 + (x157 + (x14 + (x41 + (x90 + (x74 + (x135 + (x79 + (x122 + (x63 + (x108 + (x60 + (x140 + (x168 + (x66 + (x184 + (x34 + (x164 + (x40 + (x136 + (x51 + (x85 + (x130 + (x81 + (x117 + (x160 + (x27 + (x150 + (x84 + (x86 + (x199 + (x189 + (x59 + (x105 + (x50 + (x80 + (x153 + (x58 + (x156 + (x167 + (x137 + (x102 + (x24 + (x196 + (x169 + (x88 + (x13 + (x113 + (x72 + (x176 + (x163 + (x134 + (x44 + (x54 + (x76 + (x53 + (x155 + (x107 + (x177 + (x192 + (x7 + (x110 + (x87 + (x16 + (x171 + (x67 + (x161 + (x4 + (x151 + (x15 + (x187 + (x48 + (x38 + (x6 + (x39 + (x98 + (x33 + (x61 + (x32 + (x188 + (x118 + (x18 + (x62 + (x10 + (x170 + (x174 + (x142 + (x71 + (x22 + (x132 + (x5 + (x183 + (x99 + (x112 + (x180 + (x197 + (x89 + (x49 + (x64 + (x166 + (x172 + (x47 + (x159 + (x154 + (x11 + (x91 + (x20 + (x43 + (x141 + (x26 + (x173 + (x56 + (x82 + (x129 + (x35 + (x119 + (x114 + (x165 + (x36 + (x162 + (x109 + (x121 + (x42 + (x181 + (x9 + (x182 + (x128 + (x147 + (x124 + (x52 + (x73 + (x123 + (x126 + (x116 + (x93 + (x125 + (x149 + (x145 + (x29 + (x193 + (x143 + (x0 + (x30 + (x45 + (x191 + (x127 + (x1 + (x3 + (x101 + (x77 + (x94 + (x46 + (x131 + (x146 + (x195 + (x104 + (x2 + (x8 + (x25 + (x103 + (x175 + (x198 + (x92 + (x55 + (x68 + (x17 + (x185 + (x111 + (x57 + (x37 + (x120 + (x138 + (x28 + (x96 + (x97 + (x158 + (x139 + (x75 + (x115 + (x148 + (x65 + (x31 + (x19 + (x152 + (x100 + (x78 + (x106 + (x133 + (x70 + (x83 + (x21 + (x95 + (x144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by perm_add_eq 
