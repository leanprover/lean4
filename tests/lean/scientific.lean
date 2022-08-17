-- https://github.com/leanprover/lean4/issues/1484
#eval 1.0e1    -- 10.000000
#eval 1.0e+1   -- 10.000000
#eval 1.0e-1   -- 0.1000000

#eval 1.0e     -- error
#eval 1.0e+    -- error
#eval 1.0e-    -- error
#eval 1.0e+ 1  -- error
#eval 1.0e + 1 -- error
