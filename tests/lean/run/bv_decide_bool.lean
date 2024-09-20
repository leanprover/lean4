import Std.Tactic.BVDecide

example (h : true = false) : False := by bv_decide
example {x y z : Bool} (_ : (x && y) = z) (_ : x = !y) (_ : z = true) : False := by bv_decide
example {a b c d e f : Bool} (_ : (a && b) = c) (_ : (b && c) = d) (_ : (c && d) = e) (_ : (d && e) = f)
    (_ : a = false) (_ : f = true) : False := by bv_decide

example (h : true = false) : False := by bv_decide
example (h : x = false) : false = x := by bv_decide
