/-! Incremental reuse in `mutual` -/

/-! should invalidate body of `b1` only -/

mutual
def b0 : (by dbg_trace "b 0 0"; exact Nat) := (by dbg_trace "b 0 1"; exact 0)

def b1 : (by dbg_trace "b 1 0"; exact Nat) := (by dbg_trace "b 1 1"; exact 0)
                                                                --^ sync
                                                                --^ insert: ".5"
end

/-! should invalidate both bodies (and, in current impl, second header) -/

-- RESET
mutual
def f0 : (by dbg_trace "f 0 0"; exact Nat) := (by dbg_trace "f 0 1"; exact 0)
                                                                --^ sync
                                                                --^ insert: ".5"
def f1 : (by dbg_trace "f 1 0"; exact Nat) := (by dbg_trace "f 1 1"; exact 0)
end

/-! should invalidate everything but header of `h0` -/

-- RESET
mutual
def h0 : (by dbg_trace "h 0 0"; exact Nat) := (by dbg_trace "h 0 1"; exact 0)
def h1 : (by dbg_trace "h 1 0"; exact Nat) := (by dbg_trace "h 1 1"; exact 0)
                           --^ sync
                           --^ insert: ".5"
end
