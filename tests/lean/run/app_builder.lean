definition a :num := 10

constant b : num
constant c : num
constant H1 : a = b
constant H2 : b = c
constant d : nat
constant f : nat → nat
constant g : nat → nat

set_option pp.implicit true
set_option pp.universes true
set_option pp.notation  false
(*
 local env = get_env()
 local tc  = non_irreducible_type_checker()
 local b   = app_builder(tc)
 local a   = Const("a")
 local c   = Const("c")
 local d   = Const("d")
 local f   = Const("f")
 local g   = Const("g")
 function tst(n, ...)
    local args = {...}
    local r    = b:mk_app(n, unpack(args))
    print(tostring(r) .. " : " .. tostring(tc:check(r)))
    return r
 end
 tst("eq", a, c)
 tst("eq", a, c)
 tst("eq", c, a)
 tst("eq", a, a)
 tst("eq", d, d)
 tst({"eq", "refl"}, a)
 tst({"eq", "refl"}, a)
 tst({"eq", "refl"}, d)
 tst({"eq", "refl"}, d)
 tst({"eq", "refl"}, c)
 tst({"eq", "refl"}, c, false)
 tst({"eq", "refl"}, a)
 local H1  = Const("H1")
 local H2  = Const("H2")
 tst({"eq", "trans"}, H1, H2)
 H1sy = tst({"eq", "symm"}, H1)
 H2sy = tst({"eq", "symm"}, H2)
 tst({"eq", "trans"}, H2sy, H1sy)
 tst({"heq", "refl"}, a)
 H1h = tst({"heq", "of_eq"}, H1)
 H2h = tst({"heq", "of_eq"}, H2)
 tst({"heq", "trans"}, H1h, H2h)
 tst({"heq", "symm"}, H1h)
 tst({"heq", "symm"}, H1h)
 tst({"heq"}, a, c)
 tst({"heq"}, a, d)
 tst({"heq"}, d, a)
 tst({"heq"}, a, c)
 tst({"heq"}, a, d)
 tst({"heq"}, d, a)
 tst({"eq", "refl"}, f)
 tst({"eq", "refl"}, g)
 tst("eq", f, g)
 tst("eq", g, f)
*)
