import system.io
universes u
open io

def prg (seed : nat): io unit :=
do put_str_ln ("Generating random numbers using seed: " ++ to_string seed),
   set_rand_gen (mk_std_gen seed),
   iterate 20 $ λ i,
     if i > 0 then
       do { n ← rand 0 18446744073709551616,
            put_str_ln $ to_string n,
            return $ some (i - 1) }
     else
       return none,
   return ()

#eval prg 1
#eval prg 2
