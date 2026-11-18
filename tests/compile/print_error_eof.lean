/-! Regression test for #16462: an uncaught `IO.Error.unexpectedEof` (a boxed scalar) must be printed. -/

def main : IO Unit :=
  throw IO.Error.unexpectedEof
