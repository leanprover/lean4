
def main : IO Unit :=
IO.println (strictOr false false) *>
IO.println (strictOr false true) *>
IO.println (strictOr true false) *>
IO.println (strictOr true true) *>
IO.println (strictAnd false false) *>
IO.println (strictAnd false true) *>
IO.println (strictAnd true false) *>
IO.println (strictAnd true true)
