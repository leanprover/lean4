/-! Go-to-definition and document highlight keep working on the section variables in the commands
that reuse the cached elaboration. See `Elab.cacheSectionVars`.

The cache takes an entry only after the same key misses twice, so `t3` is the first command that
reuses it. A reuse reopens the telescope and makes new free variables, and `runTermElabM` adds a
binder info node for each of them. -/

section
variable (x : Nat)

theorem t1 : x = x := rfl

theorem t2 : x = x := rfl

theorem t3 : x = x := rfl
           --^ textDocument/definition
           --^ textDocument/documentHighlight

def d4 : Nat := x
              --^ textDocument/definition

end
