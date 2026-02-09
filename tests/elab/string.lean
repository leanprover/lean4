module
set_option cbv.warning false

/-!
# Tests for `String` functions
-/
def abc : String := "abc"
def lean : String := "L∃∀N"

macro tk:"#test " t:term : command =>
  `(#guard%$tk $t
    example : $t := by decide_cbv)

/-!
Examples from documentation (added in https://github.com/leanprover/lean4/pull/4166)
-/

-- List.asString
#test ['L', '∃', '∀', 'N'].asString = "L∃∀N"
#test [].asString = ""
#test ['a', 'a', 'a'].asString = "aaa"

-- length
#test "".length = 0
#test "abc".length = 3
#test "L∃∀N".length = 4

-- push
#test "abc".push 'd' = "abcd"
#test "".push 'a' = "a"

-- append
#test "abc".append "def" = "abcdef"
#test "abc" ++ "def" = "abcdef"
#test "" ++ "" = ""

-- toList
#test "abc".toList = ['a', 'b', 'c']
#test "".toList = []
#test "\n".toList = ['\n']

-- Pos.Raw.isValid
#test String.Pos.Raw.isValid "abc" ⟨0⟩ = true
#test String.Pos.Raw.isValid "abc" ⟨1⟩ = true
#test String.Pos.Raw.isValid "abc" ⟨3⟩ = true
#test String.Pos.Raw.isValid "abc" ⟨4⟩ = false
#test String.Pos.Raw.isValid "𝒫(A)" ⟨0⟩ = true
#test String.Pos.Raw.isValid "𝒫(A)" ⟨1⟩ = false
#test String.Pos.Raw.isValid "𝒫(A)" ⟨2⟩ = false
#test String.Pos.Raw.isValid "𝒫(A)" ⟨3⟩ = false
#test String.Pos.Raw.isValid "𝒫(A)" ⟨4⟩ = true

-- get
#test "abc".get ⟨1⟩ = 'b'
#test "abc".get ⟨3⟩ = (default : Char)
#test "L∃∀N".get ⟨2⟩ = (default : Char)

-- get?
#test "abc".get? ⟨1⟩ = some 'b'
#test "abc".get? ⟨3⟩ = none
#test "L∃∀N".get? ⟨1⟩ = some '∃'
#test "L∃∀N".get? ⟨2⟩ = none

-- get!
#test "abc".get! ⟨1⟩ = 'b'

-- set
#test "abc".set ⟨1⟩ 'B' = "aBc"
#test "abc".set ⟨3⟩ 'D' = "abc"
#test "L∃∀N".set ⟨4⟩ 'X' = "L∃XN"
#test "L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"

-- modify
#test abc.modify ⟨1⟩ Char.toUpper = "aBc"
#test abc.modify ⟨3⟩ Char.toUpper = "abc"

-- next
#test abc.next ⟨3⟩ = ⟨4⟩
#test "L∃∀N".next ⟨2⟩ = ⟨3⟩
#test abc.get (0 |> abc.next) = 'b'
#test lean.get (0 |> lean.next |> lean.next) = '∀'

-- prev
#test abc.get (abc.rawEndPos |> abc.prev) = 'c'
#test lean.get (lean.rawEndPos |> lean.prev |> lean.prev |> lean.prev) = '∃'

-- front
#test "abc".front = 'a'
#test "".front = (default : Char)

-- back
#test "abc".back = 'c'
#test "".back = (default : Char)

-- atEnd
#test (0 |> abc.next |> abc.next |> abc.atEnd) = false
#test (0 |> abc.next |> abc.next |> abc.next |> abc.next |> abc.atEnd) = true
#test (0 |> lean.next |> lean.next |> lean.next |> lean.atEnd) = false
#test (0 |> lean.next |> lean.next |> lean.next |> lean.next |> lean.atEnd) = true
#test abc.atEnd ⟨4⟩ = true
#test lean.atEnd ⟨7⟩ = false
#test lean.atEnd ⟨8⟩ = true

-- get'
def getInBounds? (s : String) (p : String.Pos.Raw) : Option Char :=
  if h : s.atEnd p then none else some (s.get' p h)

#test "L∃∀N".get' ⟨2⟩ (by decide) = (default : Char)
#test "abc".get' 0 (by decide) = 'a'
#test let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'

#test getInBounds? abc ⟨1⟩ = some 'b'
#test getInBounds? abc ⟨5⟩ = none
#test getInBounds? lean ⟨4⟩ = some '∀'

-- next'
def next? (s : String) (p : String.Pos.Raw) : Option Char :=
  if h : s.atEnd p then none else s.get (s.next' p h)

#test let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'

#test next? abc ⟨1⟩ = some 'c'
#test next? abc ⟨5⟩ = none

-- posOf
#guard "abba".posOf 'a' = ⟨0⟩
#guard "abba".posOf 'z' = ⟨4⟩
#guard "L∃∀N".posOf '∀' = ⟨4⟩

-- revPosOf
#guard "abba".revPosOf 'a' = some ⟨3⟩
#guard "abba".revPosOf 'z' = none
#guard "L∃∀N".revPosOf '∀' = some ⟨4⟩

/-!
Behavior of `String.prev` (`lean_string_utf8_prev`) in special cases (see issue #9439).
-/

#test "L∃∀N".prev ⟨0⟩ = ⟨0⟩
#test "L∃∀N".prev ⟨1⟩ = ⟨0⟩
#test "L∃∀N".prev ⟨2⟩ = ⟨1⟩
#test "L∃∀N".prev ⟨3⟩ = ⟨1⟩
#test "L∃∀N".prev ⟨4⟩ = ⟨1⟩
#test "L∃∀N".prev ⟨5⟩ = ⟨4⟩
#test "L∃∀N".prev ⟨6⟩ = ⟨4⟩
#test "L∃∀N".prev ⟨7⟩ = ⟨4⟩
#test "L∃∀N".prev ⟨8⟩ = ⟨7⟩ -- rawEndPos
#test "L∃∀N".prev ⟨9⟩ = ⟨8⟩
#test "L∃∀N".prev ⟨100⟩ = ⟨99⟩ -- small value out of bounds
#test "L∃∀N".prev ⟨2 ^ 128⟩ = ⟨2 ^ 128 - 1⟩ -- large non-scalar
#test "L∃∀N".prev ⟨2 ^ 63⟩ = ⟨2 ^ 63 - 1⟩ -- scalar boundary (64-bit)
#test "L∃∀N".prev ⟨2 ^ 31⟩ = ⟨2 ^ 31 - 1⟩ -- scalar boundary (32-bit)

/-!
Behavior of `String.next` (`lean_string_utf8_next`) in special cases (see issue #9440).
-/

#test "L∃∀N".next ⟨0⟩ = ⟨1⟩
#test "L∃∀N".next ⟨1⟩ = ⟨4⟩
#test "L∃∀N".next ⟨2⟩ = ⟨3⟩
#test "L∃∀N".next ⟨3⟩ = ⟨4⟩
#test "L∃∀N".next ⟨4⟩ = ⟨7⟩
#test "L∃∀N".next ⟨5⟩ = ⟨6⟩
#test "L∃∀N".next ⟨6⟩ = ⟨7⟩
#test "L∃∀N".next ⟨7⟩ = ⟨8⟩
#test "L∃∀N".next ⟨8⟩ = ⟨9⟩
#test "L∃∀N".next ⟨9⟩ = ⟨10⟩
#test "L∃∀N".next ⟨99⟩ = ⟨100⟩ -- small value out of bounds
#test "L∃∀N".next ⟨2 ^ 128 - 1⟩ = ⟨2 ^ 128⟩ -- large non-scalar
#test "L∃∀N".next ⟨2 ^ 63 - 1⟩ = ⟨2 ^ 63⟩ -- scalar boundary (64-bit)
#test "L∃∀N".next ⟨2 ^ 31 - 1⟩ = ⟨2 ^ 31⟩ -- scalar boundary (32-bit)

-- ofByteArray
#test (String.ofByteArray ByteArray.empty (by simp)) = ""
#test (String.ofByteArray ⟨#[76, 226, 136, 131, 226, 136, 128, 78]⟩ (.intro ['L', '∃', '∀', 'N'] rfl)) = lean

#test "abc".pos? ⟨4⟩ = none
#test "L∃∀N".pos? ⟨2⟩ = none

-- #test ("abc".pos ⟨1⟩ (by decide)).get (by decide) = 'b'
#test ("abc".pos ⟨3⟩ (by decide)).get? = none
-- #test ("L∃∀N".pos ⟨1⟩ (by decide)).get (by decide) = '∃'

#test (("L∃∀N".pos ⟨0⟩ (by decide)).next (by decide)).offset = ⟨1⟩
#test (("L∃∀N".pos ⟨1⟩ (by decide)).next (by decide)).offset = ⟨4⟩
#test (("L∃∀N".pos ⟨4⟩ (by decide)).next (by decide)).offset = ⟨7⟩
#test (("L∃∀N".pos ⟨7⟩ (by decide)).next (by decide)).offset = ⟨8⟩

#test ("L∃∀N".pos ⟨0⟩ (by decide)).next?.map (·.offset) = some ⟨1⟩
#test ("L∃∀N".pos ⟨8⟩ (by decide)).next? = none
#test ("L∃∀N".pos ⟨0⟩ (by decide)).next!.offset = ⟨1⟩

#test (("L∃∀N".pos ⟨1⟩ (by decide)).prev (by decide)).offset = ⟨0⟩
#test (("L∃∀N".pos ⟨4⟩ (by decide)).prev (by decide)).offset = ⟨1⟩
#test (("L∃∀N".pos ⟨7⟩ (by decide)).prev (by decide)).offset = ⟨4⟩
#test (("L∃∀N".pos ⟨8⟩ (by decide)).prev (by decide)).offset = ⟨7⟩

#test ("L∃∀N".pos ⟨1⟩ (by decide)).prev?.map (·.offset) = some ⟨0⟩
#test ("L∃∀N".pos ⟨0⟩ (by decide)).prev? = none
#test ("L∃∀N".pos ⟨1⟩ (by decide)).prev!.offset = ⟨0⟩
