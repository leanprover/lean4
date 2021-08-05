set_option trace.compiler.ir.result true

-- should be tail calls
mutual

  partial def even (a : Nat) : Nat := if a == 0 then 1 else odd (a - 1)

  partial def odd (a : Nat) : Nat := if a == 0 then 0 else even (a - 1)

end
