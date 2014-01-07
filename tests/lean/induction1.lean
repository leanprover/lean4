import macros -- loads the take, assume, obtain macros

using Nat     -- using the Nat namespace (it allows us to suppress the Nat:: prefix)

axiom Induction : ∀ P : Nat → Bool, P 0 ⇒ (∀ n, P n ⇒ P (n + 1)) ⇒ ∀ n, P n.

-- induction on n

theorem Comm1 : ∀ n m, n + m = m + n
:= Induction
     ◂ _          -- I use a placeholder because I do not want to write the P
     ◂ (take m,   -- Base case
         calc 0 + m  = m      :  add::zerol m
                 ... = m + 0  :  symm (add::zeror m))
     ◂ (take n,   -- Inductive case
          assume (iH : ∀ m, n + m = m + n),
            take m,
               calc n + 1 + m  = (n + m) + 1  : add::succl n m
                          ...  = (m + n) + 1  : { iH ◂ m }
                          ...  = m + (n + 1)  : symm (add::succr m n))

-- indunction on m

theorem Comm2 : ∀ n m, n + m = m + n
:= take n,
     Induction
        ◂ _
        ◂ (calc n + 0  = n      :  add::zeror n
                   ... = 0 + n  :  symm (add::zerol n))
        ◂ (take m,
             assume (iH : n + m = m + n),
               calc n + (m + 1)  = (n + m) + 1  : add::succr n m
                            ...  = (m + n) + 1  : { iH }
                            ...  = (m + 1) + n  : symm (add::succl m n))


print environment 1