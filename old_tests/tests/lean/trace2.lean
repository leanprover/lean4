open tactic

declare_trace foo.bla

example : true :=
by do
  when_tracing `foo.bla $ do {
    trace "hello",
    trace "world" },
  constructor

set_option trace.foo.bla true
#print "------------"

example : true :=
by do
  when_tracing `foo.bla $ do {
    trace "hello",
    trace "world" },
  constructor
