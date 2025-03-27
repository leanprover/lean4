def f1 (a : Array Nat) (i : Nat) :=
  a[i]

def f2 (a : Array Nat) (i : Fin a.size) :=
  a[i] -- Ok

def f3 (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
  a[i] -- Ok

opaque a : Array Nat
opaque n : Nat
axiom n_lt_a_size : n < a.size

def f4 (i : Nat) (h : i < n) :=
  have : i < a.size := Nat.lt_trans h n_lt_a_size
  a[i]

def f5 (i : Nat) (h : i < n) :=
  a[i]'(Nat.lt_trans h n_lt_a_size)

def f6 (i : Nat) :=
  a[i]!

def f7 (i : Nat) :=
  a[i]?

#print f2
#print f3
#print f5
#print f6
#print f7

def withRange (xs : Array Nat) : Option Nat := Id.run do
  for h : i in [:xs.size] do
    if i == xs[i] then
      return i
  return none

def withTwoRanges (xs : Array Nat) : Option Nat := Id.run do
  for h1 : i in [:xs.size] do
    for h2 : j in [i + 1:xs.size] do
      if xs[i] == xs[j] then
        return i
  return none

def palindromeNeedsOmega (xs : Array Nat) : Bool := Id.run do
  for h : i in [:xs.size/2] do
    have : i < xs.size/2 := h.2.1 -- omega does not understand range yet
    if xs[xs.size - 1 - i] ≠ xs[i] then
      return false
  return true
