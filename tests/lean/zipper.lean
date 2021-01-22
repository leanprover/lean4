structure ListZipper (α : Type) :=
(xs : List α) (bs : List α)

-- set_option trace.compiler.ir.rc true

variable {α : Type}

namespace ListZipper

def goForward : ListZipper α → ListZipper α
| ⟨[], bs⟩    => ⟨[], bs⟩
| ⟨x::xs, bs⟩ => ⟨xs, x::bs⟩

def goBackward : ListZipper α → ListZipper α
| ⟨xs, []⟩    => ⟨xs, []⟩
| ⟨xs, b::bs⟩ => ⟨b::xs, bs⟩

def insert : ListZipper α → α → ListZipper α
| ⟨xs, bs⟩, x => ⟨xs, x::bs⟩

def erase : ListZipper α → ListZipper α
| ⟨[], bs⟩ => ⟨[], bs⟩
| ⟨x::xs, bs⟩ => ⟨xs, bs⟩

def curr [Inhabited α] : ListZipper α → α
| ⟨[], bs⟩    => arbitrary
| ⟨x::xs, bs⟩ => x

def currOpt : ListZipper α → Option α
| ⟨[], bs⟩    => none
| ⟨x::xs, bs⟩ => some x

def toList : ListZipper α → List α
| ⟨xs, bs⟩ => bs.reverse ++ xs

def atEnd (z : ListZipper α) : Bool :=
z.xs.isEmpty

end ListZipper

def List.toListZipper (xs : List α) : ListZipper α :=
⟨xs, []⟩

partial def testAux : ListZipper Nat → ListZipper Nat
| z =>
  if z.atEnd then
    z
  else if z.curr % 2 == 0 then
    testAux (z.goForward.insert 0)
  else if z.curr > 20 then
    testAux z.erase
  else
    testAux z.goForward -- testAux z.goForward

def test (xs : List Nat) : List Nat :=
(testAux xs.toListZipper).toList

#eval (IO.println (test [10, 11, 13, 20, 22, 40, 41, 11]) : IO Unit)
