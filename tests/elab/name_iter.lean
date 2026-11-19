import Lean

/-!
Tests for `Lean.Name.iter` and `Lean.Name.revIter`, the streaming versions of
`Lean.Name.components` and `Lean.Name.componentsRev`, and for related helpers such as
`Lean.Name.hasSingleComponent`.
-/

open Lean

def testNames : List Name :=
  [.anonymous, `a, `a.b.c, .mkNum `a.b 3, .mkNum .anonymous 7, .mkStr (.mkNum `x 2) "y",
   `«a.b».c, .mkNum (.mkStr (.mkStr (.mkStr `foo "_@") "Bar") "_hyg") 4]

#guard testNames.all fun n => n.iter.toList == n.components
#guard testNames.all fun n => n.revIter.toList == n.componentsRev
#guard testNames.all fun n => n.iter.toListRev == n.componentsRev
#guard testNames.all fun n => n.iter.length == n.getNumParts
#guard testNames.all fun n => n.revIter.length == n.getNumParts

#guard (`a.b.c).iter.toList == [`a, `b, `c]
#guard (`a.b.c).revIter.toList == [`c, `b, `a]
#guard (`a.b.c).iter.first? == some `a
#guard (`a.b.c).revIter.first? == some `c
#guard (Name.anonymous).iter.first? == none
#guard (Name.anonymous).revIter.first? == none
#guard (Name.mkNum `a 1).iter.toList == [`a, .mkNum .anonymous 1]
#guard (Name.mkNum `a 1).revIter.toList == [.mkNum .anonymous 1, `a]

#guard (`a.b.c).iter.any (· == `b)
#guard !(`a.b.c).revIter.any (· == `d)
#guard ((`a.b.c).iter.map (·.toString) |>.toArray) == #["a", "b", "c"]
#guard ((`a.b.c).revIter.take 2).toList == [`c, `b]

/-- `for` loops with early return. -/
def firstNumComponent? (n : Name) : Option Nat := Id.run do
  for c in n.iter do
    if let .num _ v := c then return some v
  return none

#guard firstNumComponent? (.mkStr (.mkNum (.mkNum `a 1) 2) "b") == some 1
#guard firstNumComponent? `a.b == none

#guard (`a.b.c).dropLastComponents 0 == `a.b.c
#guard (`a.b.c).dropLastComponents 1 == `a.b
#guard (`a.b.c).dropLastComponents 3 == .anonymous
#guard (`a.b.c).dropLastComponents 5 == .anonymous

#guard (`a).hasSingleComponent
#guard (Name.mkNum .anonymous 2).hasSingleComponent
#guard !(`a.b).hasSingleComponent
#guard !(Name.mkNum `a 2).hasSingleComponent
#guard !Name.anonymous.hasSingleComponent
#guard testNames.all fun n => n.hasSingleComponent == (n.getNumParts == 1)

/-! `Name.isMetaprogramming` uses `Name.revIter`. -/

#guard (`Lean.Foo).isMetaprogramming
#guard (`Foo.Meta.bar).isMetaprogramming
#guard (`Foo.Tactic).isMetaprogramming
#guard !(`Foo.Bar).isMetaprogramming
#guard !Name.anonymous.isMetaprogramming

/-! `Syntax.identComponents` uses `Name.dropLastComponents` and `Name.revIter` for `nFields`. -/

#guard (Syntax.identComponents (mkIdent `foo.bla.boo) (nFields? := some 1)).map (·.getId)
  == [`foo.bla, `boo]
#guard (Syntax.identComponents (mkIdent `foo.bla.boo) (nFields? := some 2)).map (·.getId)
  == [`foo, `bla, `boo]
#guard (Syntax.identComponents (mkIdent `foo.bla.boo) (nFields? := some 5)).map (·.getId)
  == [.anonymous, `foo, `bla, `boo]
#guard (Syntax.identComponents (mkIdent `foo.bla.boo)).map (·.getId) == [`foo, `bla, `boo]
