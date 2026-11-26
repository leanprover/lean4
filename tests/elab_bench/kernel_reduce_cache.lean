/-!
Long kernel reductions by `decide +kernel`, whose intermediate results the kernel's bounded
reduction caches must not all keep alive.
-/

set_option maxRecDepth 100000

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem foldl_range : (List.range 2000).foldl (· + ·) 0 = 1999000 := by decide +kernel

theorem sumTo_eq : sumTo 3000 = 4501500 := by decide +kernel

theorem map_range_length :
    ((List.range 300).map (fun i => (List.range i).length)).foldl (· + ·) 0 = 44850 := by
  decide +kernel
