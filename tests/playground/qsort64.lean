-- set_option trace.compiler.ir.boxing true

def main (xs : List String) : IO Unit :=
do
let a := xs.head.toNat.fold (fun i (a : Array UInt64) => a.push (UInt64.ofNat i)) Array.empty;
IO.println $ (a.qsort (fun x y => x > y)).get 0
