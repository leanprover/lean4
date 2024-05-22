/-!
# Examples from documentation added in https://github.com/leanprover/lean4/pull/4166
-/
def abc : String := "abc"
def lean : String := "L∃∀N"

#guard abc.get (0 |> abc.next) = 'b'
#guard lean.get (0 |> lean.next |> lean.next) = '∀'
#guard abc.get (abc.endPos |> abc.prev) = 'c'
#guard lean.get (lean.endPos |> lean.prev |> lean.prev |> lean.prev) = '∃'
#guard "abc".front = 'a'
#guard "".front = (default : Char)
#guard "abc".back = 'c'
#guard "".back = (default : Char)
#guard (0 |> abc.next |> abc.next |> abc.atEnd) = false
#guard (0 |> abc.next |> abc.next |> abc.next |> abc.next |> abc.atEnd) = true
#guard (0 |> lean.next |> lean.next |> lean.next |> lean.next |> lean.atEnd) = true
