import system.io

-- count the even numbers from 0 to 7 in a horrible, imperative way
def cont_example : cont_t unit (state_t ℕ io) ℕ :=
do call_cc $ λ break,
    (list.range 10).mmap' $ λ i,
      call_cc $ λ continue, do {
        when (i % 2 = 0) $
          continue (),
        when (i > 7) $
          break (),
        modify (+1) >> pure ()
      },
   get

#eval do ((), 4) ← (cont_example.run (λ _, pure ())).run 0,
         pure ()
