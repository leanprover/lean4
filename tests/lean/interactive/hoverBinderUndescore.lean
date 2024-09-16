def f : Nat → Bool → Nat :=
 fun _ _ => 5
   --^ textDocument/hover
     --^ textDocument/hover

def g : Nat → Bool → Nat :=
 fun (_ _) => 5
    --^ textDocument/hover
      --^ textDocument/hover

def h : Nat → Bool → Nat :=
 fun (_ _ : _) => 5
    --^ textDocument/hover
      --^ textDocument/hover

example (h: ∀ m : Nat, Nat.zero = m):
  Nat.zero = (Nat.zero + Nat.zero) := by show_term exact h _
                                                         --^ textDocument/hover
