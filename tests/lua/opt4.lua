local o = options({"pp", "colors"}, true, {"pp", "unicode"}, false)
print(o)
assert(not pcall(function() options({"pp", "colors"}, true, {"pp", "unicode"}) end))
assert(not pcall(function() options({"pp", "colors"}, true, {"pp", "unicodee"}, false) end))
