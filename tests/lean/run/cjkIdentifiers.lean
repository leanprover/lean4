/-!
  # CJK (Chinese, Japanese, Korean) identifier support

  This test verifies that CJK characters can be used in identifier names
  without requiring escape sequences.
-/

/-!
  ## Chinese identifiers
  Test basic Chinese character support in identifiers
-/

def 函数 : Nat := 42
def 变量 : String := "hello"
def 类型 : Type := Nat

/-- info: 42 -/
#guard_msgs in
#eval 函数

/-- info: "hello" -/
#guard_msgs in
#eval 变量

/-!
  ## Mixed Chinese and English identifiers
  Test that Chinese characters can be mixed with ASCII characters
-/

def foo_中文_bar : Bool := true
def 测试_function : Nat → Nat := fun x => x + 1

/-- info: true -/
#guard_msgs in
#eval foo_中文_bar

/-- info: 6 -/
#guard_msgs in
#eval 测试_function 5

/-!
  ## Japanese identifiers
  Test Hiragana and Katakana character support
-/

def こんにちは : String := "hello in Japanese"
def カタカナ : Nat := 123

/-- info: "hello in Japanese" -/
#guard_msgs in
#eval こんにちは

/-- info: 123 -/
#guard_msgs in
#eval カタカナ

/-!
  ## Korean identifiers
  Test Hangul character support
-/

def 한글 : String := "Korean"
def 안녕하세요 : Bool := false

/-- info: "Korean" -/
#guard_msgs in
#eval 한글

/-- info: false -/
#guard_msgs in
#eval 안녕하세요

/-!
  ## Complex expressions with CJK identifiers
  Test that CJK identifiers work in function definitions and applications
-/

def 计算 (x : Nat) (y : Nat) : Nat := x + y
def 结果 : Nat := 计算 10 20

/-- info: 30 -/
#guard_msgs in
#eval 结果

/-!
  ## CJK identifiers in structures
  Test that CJK characters work in structure field names
-/

structure 数据结构 where
  字段一 : Nat
  字段二 : String
  
def 实例 : 数据结构 := { 字段一 := 100, 字段二 := "test" }

/-- info: 100 -/
#guard_msgs in
#eval 实例.字段一

/-- info: "test" -/
#guard_msgs in
#eval 实例.字段二

/-!
  ## CJK identifiers in type classes
  Test that CJK characters work in class names and methods
-/

class 类别 (α : Type) where
  操作 : α → α → α
  
instance : 类别 Nat where
  操作 := fun x y => x + y

def 使用类别 [类别 α] (x y : α) : α := 类别.操作 x y

/-- info: 7 -/
#guard_msgs in
#eval 使用类别 3 4

/-!
  ## Escaped identifiers still work
  Verify that the escape sequence syntax continues to work
-/

def «中文测试» := 999

/-- info: 999 -/
#guard_msgs in
#eval «中文测试»