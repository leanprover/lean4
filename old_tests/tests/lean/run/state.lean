import system.io

def lifted_test : reader_t ℕ (state_t ℕ io) unit :=
do 0 ← read,  -- unlifted
   1 ← get,  -- transparently lifted through reader_t

   put 2,
   2 ← get,

   modify (+1),
   3 ← get,

   put 4 <|> put 5,
   4 ← get,  -- left branch wins

   modify (+1) >> monad_fail.fail "" <|> modify (+2),
   6 ← get,  -- an outer state_t makes the state backtrack
   pure ()

#eval (lifted_test.run 0).run 1

def infer_test {m} [monad_state ℕ m] [monad m] : m ℕ :=
do n ← get,
   -- can infer σ through class inference
   pure n.succ

def adapt_test : reader_t ℕ (state_t (ℕ × ℕ) io) unit :=
do -- zoom in on second elem
   adapt_state
     (λ p, (prod.snd p, prod.fst p)) -- note: type of `p` is not known yet
     (λ m n, (n, m))
     -- note: inner monad type must be known
     -- note: the reader_t layer is not discarded
     (read >>= put : reader_t ℕ (state_t ℕ io) punit),
   (1, 0) ← get,

   -- zoom out
   3 ← adapt_state
         (λ p, ((p, 3), p))
         (λ q _, q.1)
         ((do q ← get, pure q.2) : reader_t ℕ (state_t ((ℕ × ℕ) × ℕ) io) ℕ),
   pure ()

#eval (adapt_test.run 0).run (1, 2)

def bistate_test : state_t ℕ (state_t bool io) unit :=
do 0 ← get, -- outer state_t wins
   -- can always lift manually
   tt ← monad_lift (get : state_t bool io bool),
   pure ()

#eval (bistate_test.run 0).run tt
