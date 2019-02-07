def main (n : list string) : io uint32 :=
do io.println' (to_string n),
   pure 0
