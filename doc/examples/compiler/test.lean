@[extname main]
def my_test (n : list string) : io uint32 :=
do io.println' (to_string n),
   pure 0
