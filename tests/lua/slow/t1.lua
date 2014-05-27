function mk_big(f, depth, val)
    if depth == 1 then
       return Const{"foo", val}
    else
       return f(mk_big(f, depth - 1, 2 * val), mk_big(f, depth - 1, 2 * val + 1))
    end
end

local f  = Const("f")
local r1 = mk_big(f, 18, 0)
local r2 = mk_big(f, 18, 0)
assert(r1 == r2)
