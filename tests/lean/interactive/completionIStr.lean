structure C where
  f1 : Nat
  f2 : Bool
  b1 : String

#check fun c : C => s!"testing {c. "
                                --^ textDocument/completion
