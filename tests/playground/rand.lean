def main (xs : List String) : IO Unit :=
do [seed, n] ← pure (xs.map String.toNat) | throw "invalid number of arguments",
   IO.setRandSeed seed,
   n.mfor $ λ _, IO.rand 0 1000 >>= IO.println
