-- Return true if x is an integer
function is_integer(x)
    return math.floor(x) == x
end

-- Convert a table into a Lean options object
function to_options(t, prefix, opts)
    if opts == nil then opts = options() end
    for k, v in pairs(t) do
        if type(v) == "table" then
           opts = to_options(v, name(prefix, k), opts)
        else
           opts = opts:update(name(prefix, k), v)
        end
    end
    return opts
end

opts = options()
opts = opts:update(name('pp', 'colors'), false)
opts = opts:update(name('pp', 'colors'), true)
print(opts)

opts = to_options{pp={colors=true, width=10}}
print(opts)
