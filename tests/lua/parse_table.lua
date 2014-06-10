function display_parse_table(t)
   t:for_each(function(ts, es)
                 if not t:is_nud() then
                    io.write("_ ")
                 end
                 for i = 1, #ts do
                    io.write("'" .. tostring(ts[i][1]) .. "'")
                    local a = ts[i][2]
                    local k = a:kind()
                    if k == notation_action_kind.Skip then
                    elseif k == notation_action_kind.Binder then
                       io.write(" binder")
                    elseif k == notation_action_kind.Binders then
                       io.write(" binders")
                    elseif k == notation_action_kind.Ext then
                       io.write(" external")
                    elseif k == notation_action_kind.ScopedExpr then
                       io.write(" [_@" .. tostring(a:rbp()) .. ":" .. tostring(a:rec()) .. "]")
                    elseif k == notation_action_kind.Expr then
                       if a:rbp() == 0 then
                          io.write(" _")
                       else
                          io.write(" _@" .. tostring(a:rbp()))
                       end
                    elseif k == notation_action_kind.Exprs then
                       io.write(" [" .. tostring(a:rbp()) .. ", " .. tostring(a:rec()) .. ", " .. tostring(a:ini()) .. ", " .. tostring(a:is_fold_right()) .. "]")
                    end
                    io.write(" ")
                 end
                 print(":= ")
                 while (not es:is_nil()) do
                    print("  " .. tostring(es:head()))
                    es = es:tail()
                 end
   end)
end

function parse_table_size(t)
   local r = 0
   t:for_each(function(ts, es) r = r + #es end)
   return r
end

local p = parse_table()
assert(is_parse_table(p))
local ite  = Const("ite")
local ite2 = Const("ite2")
local If   = Const("if")
p = p:add({"if", "then", "else"}, ite(Var(0), Var(1), Var(2)))
p = p:add({"if", "then", "else"}, ite2(Var(0), Var(1), Var(2)))
p = p:add({"if", "then"}, If(Var(0), Var(1)))
display_parse_table(p)
assert(parse_table_size(p) == 3)
p = p:add({"if", "then", "else"}, ite2(Var(0), Var(1), Var(2)), false)
print("======")
display_parse_table(p)
assert(parse_table_size(p) == 2)
local f = Const("f")
p = p:add({{"with", Skip}, "value"}, f(Var(0)))
local Exists = Const("Exists")
local ExistUnique = Const("ExistUnique")
p = p:add({{"exists", Binders}, {",", scoped_expr_notation_action(Exists(Var(0)))}}, Var(0))
p = p:add({{"exist!", Binder}, {",", scoped_expr_notation_action(ExistUnique(Var(0)))}}, Var(0))
print("======")
display_parse_table(p)
check_error(function() p = p:add({{"with", Skip}, "value"}, f(Var(1))) end)
check_error(function()
               p = p:add({{",", scoped_expr_notation_action(Exists(Var(0)))}}, Var(0))
end)
local nat_add = Const({"nat", "add"})
local int_add = Const({"int", "add"})
check_error(function() p = p:add({{"+", 10}}, nat_add(Var(0), Var(1))) end)
p = p:add({"if", "then", "else"}, ite(Var(0), Var(1), Var(2)))
local a, p2 = p:find("if")
assert(is_notation_action(a))
assert(a:kind() == notation_action_kind.Expr)
assert(a:rbp() == 0)
print("======")
display_parse_table(p2)
assert(parse_table_size(p2) == 3)
local _, p2 = p2:find("then")
local _, p2 = p2:find("else")
print("======")
assert(parse_table_size(p2) == 2)
display_parse_table(p2)
local es = p2:is_accepting()
assert(es)
assert(#es == 2)

local p = parse_table(false) -- Create led table
assert(not p:is_nud())
p = p:add({{"+", 10}}, nat_add(Var(0), Var(1)))
p = p:add({{"+", 10}}, int_add(Var(0), Var(1)))
print("======")
display_parse_table(p)

local nat_mul = Const({"nat", "mul"})
local int_mul = Const({"int", "mul"})
local p2 = parse_table(false) -- Create led table
p2 = p2:add({{"*", 20}}, nat_mul(Var(0), Var(1)))
p2 = p2:add({{"*", 20}}, int_mul(Var(0), Var(1)))
print("======")
display_parse_table(p2)

p = p:merge(p2)
print("======")
display_parse_table(p)
assert(parse_table_size(p) == 4)

local p3 = parse_table()
check_error(function() p:merge(p3) end)

local a = scoped_expr_notation_action(Var(0), 10)
assert(a:use_lambda_abstraction())
local a = scoped_expr_notation_action(Var(0), 10, false)
assert(not a:use_lambda_abstraction())
local a = scoped_expr_notation_action(Var(0), 10, true)
assert(a:use_lambda_abstraction())
assert(a:rbp() == 10)
