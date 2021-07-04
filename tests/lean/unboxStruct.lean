
structure AddrSpace where
  index : UInt32

@[extern "foo"]
constant foo (addrSpace : AddrSpace) : IO PUnit

set_option trace.compiler.ir.result true in
-- should accept and pass an unboxed `uint32`
def test2 : AddrSpace → IO PUnit := foo
