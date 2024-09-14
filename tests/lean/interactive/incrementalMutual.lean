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

/-! #4328 incorrect info tree restore led to linter false-positives. -/

-- RESET
def map' {α β} (f : α → β) : List α → List β :=
  List.map f
          --^ collectDiagnostics
          --^ insert: "\n"
          --^ collectDiagnostics

/-! Reuse should work through the namespaced decl macro. -/
-- RESET
def ns.n : (by dbg_trace "ns 0"; exact Nat) := by
  dbg_trace "ns 1"
               --^ sync
               --^ insert: ".5"
  exact 0

/-! Changing the namespace should prohibit def reuse. -/
-- RESET
def nt.n : (by dbg_trace "nt 0"; exact Nat) := by
   --^ sync
   --^ change: "t" "u"
  dbg_trace "nt 1"
  exact 0

/-! Reuse should support `in`. -/
-- RESET
set_option trace.Elab.definition.body true in
def so : Nat := by
  dbg_trace "so 0"
  dbg_trace "so 1"
               --^ sync
               --^ insert: ".5"
  exact 0

/-!
Incomplete syntax should not suppress errors in previous definitions as that would prevent reuse.
-/
-- RESET
mutual
def e0 : Nat := doesNotExist
def e1 : Nat := doesNotExist
en
--^ sync
--^ insert: "d"
--^ collectDiagnostics
