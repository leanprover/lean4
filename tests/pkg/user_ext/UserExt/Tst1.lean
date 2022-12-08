import UserExt.FooExt
import UserExt.BlaExt

set_option trace.myDebug true

insert_foo hello

set_option trace.myDebug false

insert_foo world
show_foo_set

insert_bla abc
show_bla_set
