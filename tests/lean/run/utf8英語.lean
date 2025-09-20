import Lean.Util.TestExtern

deriving instance DecidableEq for ByteArray

test_extern String.toUTF8 ""
test_extern String.toUTF8 "\x00"
test_extern String.toUTF8 "$£€𐍈"

macro "test_extern'" t:term " => " v:term : command =>
  `(test_extern $t
    #guard $t == $v)

def checkGet (s : String) (arr : Array UInt8) :=
  (List.range s.utf8ByteSize).all fun i =>
    let c := if h : _ then s.getUtf8Byte ⟨i⟩ h else unreachable!
    c == arr.get! i

macro "validate" arr:term " => " "↯" : command =>
  `(test_extern' String.validateUTF8 $arr => false)
macro "validate" arr:term " => " str:term : command =>
  `(test_extern' String.validateUTF8 $arr => true
    test_extern' String.fromUTF8 $arr (with_decl_name% _validate by native_decide) => $str
    test_extern' String.toUTF8 $str => $arr
    #guard checkGet $str ($arr : ByteArray).data)

validate ⟨#[]⟩ => ""
validate ⟨#[0]⟩ => "\x00"
validate ⟨#[0x80]⟩ => ↯
validate ⟨#[0x80, 0x1]⟩ => ↯
validate ⟨#[0xc0, 0x81]⟩ => ↯
validate ⟨#[0xc8, 0x81]⟩ => "ȁ"
validate ⟨#[0xc8, 0x81, 0xc8, 0x81]⟩ => "ȁȁ"
validate ⟨#[0xe0, 0x81]⟩ => ↯
validate ⟨#[0xe0, 0x81, 0x81]⟩ => ↯
validate ⟨#[0xe1, 0x81, 0x81]⟩ => "\u1041"
validate ⟨#[0xed, 0x9f, 0xbf]⟩ => "\ud7ff"
validate ⟨#[0xed, 0xa0, 0xb0]⟩ => ↯
validate ⟨#[0xed, 0xbf, 0xbf]⟩ => ↯
validate ⟨#[0xee, 0x80, 0x80]⟩ => "\ue000"
validate ⟨#[0xf1, 0x81, 0x81, 0x81]⟩ => "񁁁"
validate ⟨#[0xf8, 0x81, 0x81, 0x81, 0x81]⟩ => ↯
validate ⟨#[0x24, 0xc2, 0xa3, 0xe2, 0x82, 0xac, 0xf0, 0x90, 0x8d, 0x88]⟩ => "$£€𐍈"

def check_eq {α} [BEq α] [Repr α] (tag : String) (expected actual : α) : IO Unit :=
  unless (expected == actual) do
    throw $ IO.userError $
      s!"assertion failure \"{tag}\":\n  expected: {repr expected}\n  actual:   {repr actual}"

def DecodeUTF8: IO Unit := do
  let str := "Hello, 英語!"
  let cs := String.toList str
  let ns := cs.map Char.toNat
  IO.println cs
  IO.println ns
  check_eq "utf-8 chars" [72, 101, 108, 108, 111, 44, 32, 33521, 35486, 33] ns
  check_eq "utf-8 bytes" #[72, 101, 108, 108, 111, 44, 32, 232, 139, 177, 232, 170, 158, 33] str.toUTF8.data
  check_eq "string eq" (some str) (String.fromUTF8? str.toUTF8)

/--
info: [H, e, l, l, o, ,,  , 英, 語, !]
[72, 101, 108, 108, 111, 44, 32, 33521, 35486, 33]
-/
#guard_msgs in
#eval DecodeUTF8
