assert(not binder_info():is_implicit())
assert(not binder_info():is_cast())
assert(not binder_info(false, false):is_implicit())
assert(not binder_info(false, false):is_cast())
assert(binder_info(true):is_implicit())
assert(not binder_info(true):is_cast())
assert(binder_info(true, true):is_implicit())
assert(binder_info(true, true):is_cast())

