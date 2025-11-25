abbrev natrec_inner {C} (n: Nat)
  (z: Option C) (s: C -> Option C)
  : Option C
  := match n with
  | 0 => z
  | n + 1 => (natrec_inner n z s).bind s

def natrec_int {C} (n: Option Nat) -- ERROR
  (z: Option C) (s: C -> Option C)
  : Option C
  := n.bind (λn => natrec_inner n z s)


@[inline_if_reduce]
def foo (xs : List Nat) :=
  match xs with
  | [] => 0
  | _::xs => foo xs + 1

def error : Nat := -- ERROR
  foo [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]

set_option compiler.maxRecInlineIfReduce 32
def ok : Nat :=
  foo [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]

@[inline]
def foldr (f : Nat → β → β) (acc : β) : Nat → β
| 0 => acc
| n+1 => foldr f (f n acc) n

def toList (r : Nat) : List Nat :=
  foldr (· :: ·) [] r
