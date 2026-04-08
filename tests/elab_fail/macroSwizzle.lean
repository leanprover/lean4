notation "swizzle" a:max b => b + a

-- should *not* produce a negative span
#check swizzle "s" true

#check "x" |> Nat.succ
