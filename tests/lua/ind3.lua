function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(env:normalize(env:type_check(t))))
end

local env      = environment()
local nat      = Const("nat")
local zero     = Const("zero")
local succ     = Const("succ")

env = add_inductive(env,
                    "nat", Type,
                    "zero", nat,
                    "succ", mk_arrow(nat, nat))

local a           = Local("a", nat)
local b           = Local("b", nat)
local n           = Local("n", nat)
local r           = Local("r", nat)
local nat_rec_nat = Const({"nat", "rec"}, {1})(Fun(a, nat))
local add         = Fun(a, b, nat_rec_nat(b, Fun(n, r, succ(r)), a))
local tc          = type_checker(env)
assert(tc:is_def_eq(add(succ(succ(zero)), succ(zero)),
                    succ(succ(succ(zero)))))

print(env:normalize(add(succ(succ(zero)), succ(succ(succ(zero))))))

local l           = param_univ("l")
local U_l         = mk_sort(l)
local U_l1        = mk_sort(max_univ(l, 1))
local tree_l      = Const("tree", {l})
local tree_list_l = Const("tree_list", {l})
local A           = Local("A", U_l)
local v           = Local("v", A)
local children    = Local("children", tree_list_l(A))
local head        = Local("head", tree_l(A))
local tail        = Local("tail", tree_list_l(A))

env = add_inductive(env, {l}, 1,
                    {"tree", Pi(A, U_l1),
                     "leaf", Pi(A, tree_l(A)),
                     "node", Pi(A, v, children, tree_l(A))
                    },
                    {"tree_list", Pi(A, U_l1),
                     "nil",       Pi(A, tree_list_l(A)),
                     "cons",      Pi(A, head, tail, tree_list_l(A))})

local tree_nat        = Const("tree", {1})(nat)
local tree_list_nat   = Const("tree_list", {1})(nat)
local t               = Local("t", tree_nat)
local tl              = Local("tl", tree_list_nat)
local tree_rec_nat    = Const({"tree", "rec"}, {1, 1})(nat, Fun(t, nat), Fun(tl, nat))
local r1              = Local("r1", nat)
local r2              = Local("r2", nat)
local length_tree_nat = Fun(t, tree_rec_nat(zero,
                                            Fun(a, tl, r, succ(r)),
                                            zero,
                                            Fun(t, tl, r1, r2, add(r1, r2)),
                                            t))

display_type(env, length_tree_nat)

local leaf_nat = Const("leaf", {1})(nat)
local node_nat = Const("node", {1})(nat)
local nil_nat  = Const("nil", {1})(nat)
local cons_nat = Const("cons", {1})(nat)
local one      = succ(zero)
local two      = succ(one)
local tree1    = node_nat(one, nil_nat)
local tree2    = node_nat(two, cons_nat(leaf_nat, cons_nat(leaf_nat, nil_nat)))
local tree3    = node_nat(one, cons_nat(tree1, cons_nat(tree2, nil_nat)))
local tree4    = node_nat(one, cons_nat(tree3, cons_nat(tree3, nil_nat)))
display_type(env, tree4)
print("norm(tree1): " .. tostring(env:normalize(length_tree_nat(tree1))))
print("norm(tree2): " .. tostring(env:normalize(length_tree_nat(tree2))))
print("norm(tree3): " .. tostring(env:normalize(length_tree_nat(tree3))))
print("norm(tree4): " .. tostring(env:normalize(length_tree_nat(tree4))))
assert(env:normalize(length_tree_nat(tree1)) == succ(zero))
assert(env:normalize(length_tree_nat(tree2)) == succ(zero))
assert(env:normalize(length_tree_nat(tree3)) == succ(succ(succ(zero))))
assert(env:normalize(length_tree_nat(tree4)) == succ(succ(succ(succ(succ(succ(succ(zero))))))))
