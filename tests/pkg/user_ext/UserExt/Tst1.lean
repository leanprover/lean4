import UserExt.FooExt
import UserExt.BlaExt

#eval show IO Unit from do
  assert! fooFloat == 1.2
  assert! foo8 == 12
  assert! foo16 == 1234
  assert! foo32 == 1234
  assert! foo64 == 1234
  assert! fooNat == 1234
  assert! fooProd == (1234, true)

set_option trace.myDebug true

insert_foo hello

set_option trace.myDebug false

insert_foo world
show_foo_set

insert_bla abc
show_bla_set
