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

-- get'
#guard "abc".get' 0 (by decide) = 'a'
#guard let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'
def getInBounds? (s : String) (p: String.Pos) : Option Char :=
  if h : s.atEnd p then none else some (s.get' p h)
#guard getInBounds? abc ⟨1⟩ = some 'b'
#guard getInBounds? abc ⟨5⟩ = none
#guard getInBounds? lean ⟨4⟩ = some '∀'
#guard "L∃∀N".get' ⟨2⟩ (by decide) = (default : Char)

-- next'
#guard let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'
def next? (s: String) (p: String.Pos) : Option Char :=
  if h : s.atEnd p then none else s.get (s.next' p h)
#guard next? abc ⟨1⟩ = some 'c'
#guard next? abc ⟨5⟩ = none

-- posOf
#guard "abba".posOf 'a' = ⟨0⟩
#guard "abba".posOf 'z' = ⟨4⟩
#guard "L∃∀N".posOf '∀' = ⟨4⟩

-- revPosOf
#guard "abba".revPosOf 'a' = some ⟨3⟩
#guard "abba".revPosOf 'z' = none
#guard "L∃∀N".revPosOf '∀' = some ⟨4⟩
