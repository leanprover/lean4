import init.data.hashable

def main (xs : List String): IO Unit :=
do IO.println $ hash xs.head,
   IO.println $ hash xs.head.toNat,
   IO.println $ mixHash 1 2,
   pure ()
