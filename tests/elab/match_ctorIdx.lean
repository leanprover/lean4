def test1 (x1 x2 : List α) (h : x2.ctorIdx = x1.ctorIdx) : Bool :=
  match x1, x2, h with
  | .nil, .nil, _h => true
  | .cons _h1 _t1, .cons _h2 _t2, _h => false
  -- NB: This is a complete pattern match
