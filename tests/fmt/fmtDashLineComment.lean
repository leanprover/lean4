/-!
Tests line comments of only dashes that end in spaces. The formatter drops trailing spaces, so they
do not decide whether `--` is followed by a space. Each dash-only comment below ends in a space.
-/

---------- 
def a := 1 -- - 

-- ---- 
def b := 2

-- first
-- --- 
def c := 3
