structure AddrSpace where
  index : UInt32

@[extern "foo"]
opaque foo (addrSpace : AddrSpace) : IO PUnit

set_option trace.Compiler.result true in
set_option pp.letVarTypes true in
set_option pp.funBinderTypes true in
-- should accept and pass an unboxed `uint32`
def test2 : AddrSpace → IO PUnit := foo
