syntax "foo" &"bla" term : term

macro_rules
  | `(foo bla $x) => x

-- bla is still a valid identifier
def bla := 10

#check foo bla 10

#check foo bll 10 -- Error: expected 'bla' at 'bll'
