open tactic

example : true :=
by do
  when_tracing `app_builder $ do {
    trace "hello",
    trace "world" },
  constructor

set_option trace.app_builder true
#print "------------"

example : true :=
by do
  when_tracing `app_builder $ do {
    trace "hello",
    trace "world" },
  constructor
