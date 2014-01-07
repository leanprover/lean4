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
          assume iH,
            take m,
               calc n + 1 + m  = (n + m) + 1  : add::succl n m
                          ...  = (m + n) + 1  : { iH }  -- Error is here
                          ...  = m + (n + 1)  : symm (add::succr m n))

