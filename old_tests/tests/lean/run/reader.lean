import system.io

def lifted_test : state_t ℕ (reader_t ℕ io) unit :=
do 0 ← get,
   1 ← read,
   adapt_reader (λ n, (n, 2)) ((do p ← read,
                                   put p.2) : state_t ℕ (reader_t (ℕ × ℕ) io) _),
   2 ← get,
   pure ()

#eval (lifted_test.run 0).run 1
