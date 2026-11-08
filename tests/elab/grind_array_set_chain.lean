/-!
Congruent terms whose types differ only in `(a.set! ...).size` versus `a.size`. Checking whether
such types are definitionally equal at default transparency is exponential in the length of the
`Array.set!` chain. The terms are nested proofs `j < (a.set! ...).size` or values of dependent
types such as `Fin (a.set! ...).size` and `Vector Nat (a.set! ...).size`.
-/

set_option maxHeartbeats 20000 in
example (a : Array Nat) (j i0 v0 i1 v1 i2 v2 i3 v3 i4 v4 i5 v5 : Nat)
    (h0 : i0 ≠ j) (h1 : i1 ≠ j) (h2 : i2 ≠ j) (h3 : i3 ≠ j) (h4 : i4 ≠ j) (h5 : i5 ≠ j) :
    ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5)[j]! = a[j]! := by
  grind

set_option maxHeartbeats 50000 in
example (a : Array Nat) (j i0 v0 i1 v1 i2 v2 i3 v3 i4 v4 i5 v5 i6 v6 i7 v7 i8 v8 i9 v9 i10 v10 i11 v11 : Nat)
    (h0 : i0 ≠ j) (h1 : i1 ≠ j) (h2 : i2 ≠ j) (h3 : i3 ≠ j) (h4 : i4 ≠ j) (h5 : i5 ≠ j)
    (h6 : i6 ≠ j) (h7 : i7 ≠ j) (h8 : i8 ≠ j) (h9 : i9 ≠ j) (h10 : i10 ≠ j) (h11 : i11 ≠ j) :
    ((((((((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).set! i6 v6).set! i7 v7).set! i8 v8).set! i9 v9).set! i10 v10).set! i11 v11)[j]! = a[j]! := by
  grind (gen := 16)

set_option maxHeartbeats 20000 in
example (a : Array Nat) (k : Nat) (i0 v0 i1 v1 i2 v2 i3 v3 i4 v4 i5 v5 : Nat) (g : (m : Nat) → Fin m → Nat)
    (h1 : k < ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size) (h2 : k < a.size)
    (hs : ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size = a.size) :
    g ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size ⟨k, h1⟩ = g a.size ⟨k, h2⟩ := by
  grind only

set_option maxHeartbeats 20000 in
example (a : Array Nat) (k : Nat) (i0 v0 i1 v1 i2 v2 i3 v3 i4 v4 i5 v5 : Nat) (g : (m : Nat) → Fin m → Nat)
    (h1 : k < ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size) (h2 : k < a.size) :
    g ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size ⟨k, h1⟩ = g a.size ⟨k, h2⟩ := by
  grind

set_option maxHeartbeats 20000 in
example (a : Array Nat) (i0 v0 i1 v1 i2 v2 i3 v3 i4 v4 i5 v5 : Nat) (f : (m : Nat) → Vector Nat m) :
    (f ((((((a.set! i0 v0).set! i1 v1).set! i2 v2).set! i3 v3).set! i4 v4).set! i5 v5).size).toArray = (f a.size).toArray := by
  grind
