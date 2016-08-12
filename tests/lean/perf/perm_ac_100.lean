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


constants (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99  : X)
---------
example : x40 + (x67 + (x85 + (x35 + (x89 + (x82 + (x56 + (x14 + (x4 + (x6 + (x5 + (x11 + (x19 + (x78 + (x81 + (x63 + (x37 + (x25 + (x43 + (x45 + (x94 + (x16 + (x84 + (x54 + (x90 + (x68 + (x86 + (x9 + (x10 + (x24 + (x99 + (x64 + (x13 + (x0 + (x95 + (x80 + (x46 + (x55 + (x1 + (x97 + (x17 + (x20 + (x18 + (x87 + (x50 + (x38 + (x79 + (x7 + (x57 + (x88 + (x8 + (x75 + (x44 + (x66 + (x23 + (x98 + (x28 + (x31 + (x61 + (x51 + (x59 + (x39 + (x36 + (x41 + (x93 + (x58 + (x29 + (x91 + (x26 + (x47 + (x65 + (x22 + (x27 + (x42 + (x77 + (x62 + (x33 + (x32 + (x48 + (x34 + (x49 + (x60 + (x12 + (x73 + (x83 + (x92 + (x74 + (x15 + (x52 + (x69 + (x21 + (x30 + (x96 + (x76 + (x70 + (x3 + (x71 + (x2 + (x72 + (x53))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = x59 + (x15 + (x66 + (x88 + (x8 + (x78 + (x29 + (x18 + (x21 + (x39 + (x86 + (x81 + (x46 + (x95 + (x23 + (x84 + (x36 + (x54 + (x69 + (x0 + (x55 + (x4 + (x93 + (x31 + (x13 + (x34 + (x76 + (x11 + (x32 + (x26 + (x75 + (x37 + (x89 + (x7 + (x41 + (x28 + (x91 + (x27 + (x62 + (x42 + (x50 + (x85 + (x92 + (x72 + (x77 + (x49 + (x10 + (x38 + (x52 + (x30 + (x57 + (x96 + (x98 + (x80 + (x67 + (x44 + (x61 + (x70 + (x45 + (x65 + (x94 + (x19 + (x1 + (x99 + (x82 + (x14 + (x79 + (x22 + (x24 + (x63 + (x58 + (x68 + (x48 + (x6 + (x64 + (x25 + (x83 + (x5 + (x43 + (x73 + (x12 + (x60 + (x71 + (x17 + (x9 + (x2 + (x20 + (x51 + (x3 + (x56 + (x35 + (x40 + (x74 + (x53 + (x16 + (x47 + (x33 + (x87 + (x97 + (x90))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by perm_add_eq
