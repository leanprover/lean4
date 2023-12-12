/-!
This module systematically tests various indentation variants related to `where` and
`termination_by`/`decreasing_by`.

The naming convention is `Ex<a><b><c><d><e>.foo` where

* `a` is the column of `def`
* `b` is the column of `where
* `c` is the column of `bar` (or `h` if `bar` is hanging after the `where`)
* `d` is the column of `bar`’s `decreasing_by` (or `_` if `bar` is not recursive)
* `e` is the column of `foo`’s `decreasing_by` (or `_` if `foo` is not recursive)

-/

-- For concise recursive definition that need well-founded recursion
-- and `decreasing_by` tactics that would fail if run on the wrong function
opaque dec1 : Nat → Nat
axiom dec1_lt (n : Nat) : dec1 n < n
opaque dec2 : Nat → Nat
axiom dec2_lt (n : Nat) : dec2 n < n

def Ex00000.foo (n : Nat) := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex0000_.foo (n : Nat) := bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt

-- This combination is not supported
def Ex000_0.foo (n : Nat) := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt -- picked up by bar

def Ex00002.foo (n : Nat) := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt
  decreasing_by apply dec1_lt

-- This combination is not supported
def Ex000_2.foo (n : Nat) := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := bar m
  decreasing_by apply dec1_lt -- picked up by bar

def Ex00020.foo (n : Nat) := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex0002_.foo (n : Nat) := bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt

-- Not supported
def Ex00200.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

-- Not supported
def Ex0020_.foo (n : Nat) := bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented

def Ex002_0.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

-- Not supported
def Ex00202.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
  decreasing_by apply dec1_lt

-- This combination is not supported
def Ex002_2.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar m
  decreasing_by apply dec1_lt -- picked up by bar

def Ex00220.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex00240.foo (n : Nat) := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex0022_.foo (n : Nat) := bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt

def Ex0042_.foo (n : Nat) := bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt

-- Not supported
def Ex02200.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

-- Not supported
def Ex0220_.foo (n : Nat) := bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented

def Ex022_0.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

-- Not supported
def Ex02202.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
  decreasing_by apply dec1_lt

-- This combination is not supported
def Ex022_2.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := bar m
  decreasing_by apply dec1_lt -- picked up by bar

def Ex02220.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex02240.foo (n : Nat) := foo (dec1 n) + bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex0222_.foo (n : Nat) := bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt

def Ex0224_.foo (n : Nat) := bar n
  where
  bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt

-- Not supported
def Ex02400.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

-- Not supported
def Ex0240_.foo (n : Nat) := bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented

def Ex024_0.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

-- Not supported
def Ex02402.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
  decreasing_by apply dec1_lt

-- This combination is not supported
def Ex024_2.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar m
  decreasing_by apply dec1_lt -- picked up by bar

-- Not supported
def Ex02420.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

def Ex02440.foo (n : Nat) := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

-- Not supported
def Ex0242_.foo (n : Nat) := bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt -- needs to be indented

def Ex0244_.foo (n : Nat) := bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt

-- Not supported
def Ex00h00.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

-- Not supported
def Ex00h0_.foo (n : Nat) := bar n
where bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented

def Ex00h_0.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

-- Not supported
def Ex00h02.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt -- needs to be indented
  decreasing_by apply dec1_lt

-- This combination is not supported
def Ex00h_2.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar m
  decreasing_by apply dec1_lt -- picked up by bar

-- Not supported
def Ex00h20.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt -- needs to be indented
decreasing_by apply dec1_lt

def Ex00h40.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt -- Needs to be indented
decreasing_by apply dec1_lt

def Ex00h60.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
      decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex00h80.foo (n : Nat) := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
        decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

-- Not supported
def Ex00h2_.foo (n : Nat) := bar n
where bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt -- Needs to be indented

-- Not supported
def Ex00h4_.foo (n : Nat) := bar n
where bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt -- Needs to be indented

def Ex00h6_.foo (n : Nat) := bar n
where bar (m : Nat) : Nat := bar (dec2 m)
      decreasing_by apply dec2_lt

def Ex00h8_.foo (n : Nat) := bar n
where bar (m : Nat) : Nat := bar (dec2 m)
        decreasing_by apply dec2_lt
