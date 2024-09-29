/- arithmetic | commutativity -/

example (a b c d : BitVec w) :
    a * b * c * d = d * c * b * a := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a * b * c * d = d * c * b * a := by
  ac_rfl

example (a b c d : BitVec w) :
    a + b + c + d = d + c + b + a := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a + b + c + d = d + c + b + a := by
  ac_rfl

/- arithmetic | associativity -/

example (a b c d : BitVec w) :
    a * (b * (c * d)) = ((a * b) * c) * d := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a * (b * (c * d)) = ((a * b) * c) * d := by
  ac_rfl

example (a b c d : BitVec w) :
    a + (b + (c + d)) = ((a + b) + c) + d := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a + (b + (c + d)) = ((a + b) + c) + d := by
  ac_rfl

/- bitwise operations | commutativity -/

example (a b c d : BitVec w) :
    a ^^^ b ^^^ c ^^^ d = d ^^^ c ^^^ b ^^^ a := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a ^^^ b ^^^ c ^^^ d = d ^^^ c ^^^ b ^^^ a := by
  ac_rfl

example (a b c d : BitVec w) :
    a &&& b &&& c &&& d = d &&& c &&& b &&& a := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a &&& b &&& c &&& d = d &&& c &&& b &&& a := by
  ac_rfl

example (a b c d : BitVec w) :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  ac_rfl

/- bitwise operations | associativity -/

example (a b c d : BitVec w) :
    a &&& (b &&& (c &&& d)) = ((a &&& b) &&& c) &&& d := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a &&& (b &&& (c &&& d)) = ((a &&& b) &&& c) &&& d := by
  ac_rfl

example (a b c d : BitVec w) :
    a ||| (b ||| (c ||| d)) = ((a ||| b) ||| c) ||| d := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a ||| (b ||| (c ||| d)) = ((a ||| b) ||| c) ||| d := by
  ac_rfl

example (a b c d : BitVec w) :
    a ^^^ (b ^^^ (c ^^^ d)) = ((a ^^^ b) ^^^ c) ^^^ d := by
  ac_nf
  rfl

example (a b c d : BitVec w) :
    a ^^^ (b ^^^ (c ^^^ d)) = ((a ^^^ b) ^^^ c) ^^^ d := by
  ac_rfl
