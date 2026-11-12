module

meta import Init.Data.String
import all Init.Data.String.Basic

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

-- String.ofList
#test String.ofList ['L', '∃', '∀', 'N'] = "L∃∀N"
#test String.ofList [] = ""
#test String.ofList ['a', 'a', 'a'] = "aaa"

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
#test String.Pos.Raw.get "abc" ⟨1⟩ = 'b'
#test String.Pos.Raw.get "abc" ⟨3⟩ = (default : Char)
#test String.Pos.Raw.get "L∃∀N" ⟨2⟩ = (default : Char)

-- get?
#test String.Pos.Raw.get? "abc" ⟨1⟩ = some 'b'
#test String.Pos.Raw.get? "abc" ⟨3⟩ = none
#test String.Pos.Raw.get? "L∃∀N" ⟨1⟩ = some '∃'
#test String.Pos.Raw.get? "L∃∀N" ⟨2⟩ = none

-- get!
#test String.Pos.Raw.get! "abc" ⟨1⟩ = 'b'

-- set
#test String.Pos.Raw.set "abc" ⟨1⟩ 'B' = "aBc"
#test String.Pos.Raw.set "abc" ⟨3⟩ 'D' = "abc"
#test String.Pos.Raw.set "L∃∀N" ⟨4⟩ 'X' = "L∃XN"
#test String.Pos.Raw.set "L∃∀N" ⟨2⟩ 'X' = "L∃∀N"

-- modify
#test String.Pos.Raw.modify abc ⟨1⟩ Char.toUpper = "aBc"
#test String.Pos.Raw.modify abc ⟨3⟩ Char.toUpper = "abc"

-- next
#test String.Pos.Raw.next abc ⟨3⟩ = ⟨4⟩
#test String.Pos.Raw.next "L∃∀N" ⟨2⟩ = ⟨3⟩
#test String.Pos.Raw.get abc (0 |> String.Pos.Raw.next abc) = 'b'
#test String.Pos.Raw.get lean (0 |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean) = '∀'

-- prev
#test String.Pos.Raw.get abc (abc.rawEndPos |> String.Pos.Raw.prev abc) = 'c'
#test String.Pos.Raw.get lean (lean.rawEndPos |> String.Pos.Raw.prev lean |> String.Pos.Raw.prev lean |> String.Pos.Raw.prev lean) = '∃'

-- front
#test "abc".front = 'a'
#test "".front = (default : Char)

-- back
#test "abc".back = 'c'
#test "".back = (default : Char)

-- atEnd
#test (0 |> String.Pos.Raw.next abc |> String.Pos.Raw.next abc |> String.Pos.Raw.atEnd abc) = false
#test (0 |> String.Pos.Raw.next abc |> String.Pos.Raw.next abc |> String.Pos.Raw.next abc |> String.Pos.Raw.next abc |> String.Pos.Raw.atEnd abc) = true
#test (0 |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean |> String.Pos.Raw.atEnd lean) = false
#test (0 |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean |> String.Pos.Raw.atEnd lean) = true
#test String.Pos.Raw.atEnd abc ⟨4⟩ = true
#test String.Pos.Raw.atEnd lean ⟨7⟩ = false
#test String.Pos.Raw.atEnd lean ⟨8⟩ = true

-- get'
def getInBounds? (s : String) (p : String.Pos.Raw) : Option Char :=
  if h : String.Pos.Raw.atEnd s p then none else some (String.Pos.Raw.get' s p h)

#test String.Pos.Raw.get' "L∃∀N" ⟨2⟩ (by decide) = (default : Char)
#test String.Pos.Raw.get' "abc" 0 (by decide) = 'a'
#test let lean := "L∃∀N"; String.Pos.Raw.get' lean (0 |> String.Pos.Raw.next lean |> String.Pos.Raw.next lean) (by decide) = '∀'

#test getInBounds? abc ⟨1⟩ = some 'b'
#test getInBounds? abc ⟨5⟩ = none
#test getInBounds? lean ⟨4⟩ = some '∀'

-- next'
def next? (s : String) (p : String.Pos.Raw) : Option Char :=
  if h : String.Pos.Raw.atEnd s p then none else String.Pos.Raw.get s (String.Pos.Raw.next' s p h)

#test let abc := "abc"; String.Pos.Raw.get abc (String.Pos.Raw.next' abc 0 (by decide)) = 'b'

#test next? abc ⟨1⟩ = some 'c'
#test next? abc ⟨5⟩ = none

/-!
Behavior of `String.Pos.Raw.prev` (`lean_string_utf8_prev`) in special cases (see issue #9439).
-/

#test String.Pos.Raw.prev "L∃∀N" ⟨0⟩ = ⟨0⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨1⟩ = ⟨0⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨2⟩ = ⟨1⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨3⟩ = ⟨1⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨4⟩ = ⟨1⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨5⟩ = ⟨4⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨6⟩ = ⟨4⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨7⟩ = ⟨4⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨8⟩ = ⟨7⟩ -- rawEndPos
#test String.Pos.Raw.prev "L∃∀N" ⟨9⟩ = ⟨8⟩
#test String.Pos.Raw.prev "L∃∀N" ⟨100⟩ = ⟨99⟩ -- small value out of bounds
#test String.Pos.Raw.prev "L∃∀N" ⟨2 ^ 128⟩ = ⟨2 ^ 128 - 1⟩ -- large non-scalar
#test String.Pos.Raw.prev "L∃∀N" ⟨2 ^ 63⟩ = ⟨2 ^ 63 - 1⟩ -- scalar boundary (64-bit)
#test String.Pos.Raw.prev "L∃∀N" ⟨2 ^ 31⟩ = ⟨2 ^ 31 - 1⟩ -- scalar boundary (32-bit)

/-!
Behavior of `String.Pos.Raw.next` (`lean_string_utf8_next`) in special cases (see issue #9440).
-/

#test String.Pos.Raw.next "L∃∀N" ⟨0⟩ = ⟨1⟩
#test String.Pos.Raw.next "L∃∀N" ⟨1⟩ = ⟨4⟩
#test String.Pos.Raw.next "L∃∀N" ⟨2⟩ = ⟨3⟩
#test String.Pos.Raw.next "L∃∀N" ⟨3⟩ = ⟨4⟩
#test String.Pos.Raw.next "L∃∀N" ⟨4⟩ = ⟨7⟩
#test String.Pos.Raw.next "L∃∀N" ⟨5⟩ = ⟨6⟩
#test String.Pos.Raw.next "L∃∀N" ⟨6⟩ = ⟨7⟩
#test String.Pos.Raw.next "L∃∀N" ⟨7⟩ = ⟨8⟩
#test String.Pos.Raw.next "L∃∀N" ⟨8⟩ = ⟨9⟩
#test String.Pos.Raw.next "L∃∀N" ⟨9⟩ = ⟨10⟩
#test String.Pos.Raw.next "L∃∀N" ⟨99⟩ = ⟨100⟩ -- small value out of bounds
#test String.Pos.Raw.next "L∃∀N" ⟨2 ^ 128 - 1⟩ = ⟨2 ^ 128⟩ -- large non-scalar
#test String.Pos.Raw.next "L∃∀N" ⟨2 ^ 63 - 1⟩ = ⟨2 ^ 63⟩ -- scalar boundary (64-bit)
#test String.Pos.Raw.next "L∃∀N" ⟨2 ^ 31 - 1⟩ = ⟨2 ^ 31⟩ -- scalar boundary (32-bit)

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

#test String.Pos.Raw.extract "red green blue" ⟨0⟩ ⟨3⟩ = "red"
#test String.Pos.Raw.extract "red green blue" ⟨3⟩ ⟨0⟩ = ""
#test String.Pos.Raw.extract "red green blue" ⟨0⟩ ⟨100⟩ = "red green blue"
#test String.Pos.Raw.extract "red green blue" ⟨4⟩ ⟨100⟩ = "green blue"
#test String.Pos.Raw.extract "red green blue" ⟨0⟩ ⟨2 ^ 100⟩ = "red green blue"
#test String.Pos.Raw.extract "red green blue" ⟨4⟩ ⟨2 ^ 100⟩ = "green blue"
#test String.Pos.Raw.extract "L∃∀N" ⟨1⟩ ⟨2⟩ = "∃∀N"
#test String.Pos.Raw.extract "L∃∀N" ⟨3⟩ ⟨2⟩ = ""
#test String.Pos.Raw.extract "L∃∀N" ⟨2⟩ ⟨100⟩ = ""
#test String.Pos.Raw.extract "L∃∀N" ⟨2 ^ 100⟩ ⟨1⟩ = ""
#test String.Pos.Raw.extract "L∃∀N" ⟨2 ^ 100⟩ ⟨2 ^ 101⟩ = ""

#test "red green blue".extract (String.pos _ ⟨0⟩ (by decide)) (String.pos _ ⟨3⟩ (by decide)) = "red"
#test "red green blue".extract (String.pos _ ⟨4⟩ (by decide)) (String.pos _ ⟨14⟩ (by decide)) = "green blue"
