def f (stx : Lean.Syntax) :=
  match stx with
  | `($f $a)  => 1
  | `($_)     => 2
  | `($f $b)  => 3
  | _         => "hello"
