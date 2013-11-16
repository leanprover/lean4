(**
 -- This example ask uses the parses to process a Lean string that
 -- contains a nested script block. The nexted script block will
 -- invoke the leanlua_state recursively. It also demonstrates that we
 -- need to use std::recursive_mutex instead of std::mutex at
 -- leanlua_state. Otherwise, it will deadlock trying to get a lock on
 -- the mutex.
 code = "(*" .. "*" .. "print('hello')" .. "*" .. "*)"
 print("executing: " .. code)
 parse_lean_cmds(code)
**)
