prelude

/-! Completing declaration names in arbitrary namespaces -/

axiom Lean.Elab.Term.elabTermEnsuringType : Type
axiom Lean.Elab.Tactic.elabTermEnsuringType : Type

-- adding full namespace

#check elabTermEnsuring
                     --^ textDocument/completion

-- adding partial namespace

open Lean.Elab in
#check elabTermEnsuring
                     --^ textDocument/completion

-- direct + indirect match

open Lean.Elab.Term in
#check elabTermEnsuring
                     --^ textDocument/completion

-- same, on the top level

axiom elabTermEnsuringType : Type
#check elabTermEnsuring
                     --^ textDocument/completion

-- prioritize smaller prefixes

axiom Lean.Elab.elabTermEnsuringType : Type
#check elabTermEnsuring
                     --^ textDocument/completion
