-- https://github.com/leanprover/lean4/issues/1484
#eval 1.0e1
#eval 1.0e+1
#eval 1.0e-1
#eval 1.453e-8
#eval 0.05843E5
#eval 8.43e6
#eval 5.2342E-7
#eval 123.
#eval 123.E+3
#eval -853.4E-2

-- we reject leading decimal points
#eval .123
#eval .123E3
#eval .123E00003

-- errors
#eval e-8
#eval 1.0e
#eval 1.0e+
#eval 1.0e-
#eval 1.0e+ 1
#eval 1.0e + 1
#eval 123E
#eval .E+03
#eval -E3
#eval 2e.2
