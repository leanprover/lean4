def foo1 {β} (i : ∀ α, List α) : List β := i β
                  --^ textDocument/hover

def foo2 (i : ∀ α, List α) : List β := i β
              --^ textDocument/hover

def foo3 (i : (α : _) → List α) : List β := i β
              --^ textDocument/hover

def foo4 (i : (α : id _) → List α) : List β := i β
              --^ textDocument/hover

def foo5 (i : (α : Type _) → List α) : List β := i β
              --^ textDocument/hover

def foo6 (i : (α : Type 0) → List α) : List β := i β
              --^ textDocument/hover
