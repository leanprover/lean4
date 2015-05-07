import data.finset.basic

open finset

check ∅                 -- o.k.
check λs t, subset s t  -- o.k.
check λs t, s ⊆ t       -- fixed

infix `⊆`:50 := subset
check λs t, s ⊆ t
