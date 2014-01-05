import Int.
variables a b : Int
print options
(*
  local ios = io_state()

  print(get_options())
  print(get_options())
  ios:print(parse_lean("a + b"))
  print(parse_lean("fun x, a + x"))
  print(get_options())
*)
print options
print environment 2