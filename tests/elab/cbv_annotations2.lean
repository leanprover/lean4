module
import Std

open Std

def isPalindrome (s : String) : Bool :=
  s.chars.zip s.revChars |>.all (fun p => p.1 == p.2)

example : isPalindrome "" = true := by cbv
example : isPalindrome "aba" = true := by cbv
example : isPalindrome "aaaaa" = true := by cbv
example : isPalindrome "zbcd" = false := by cbv
example : isPalindrome "xywyx" = true := by cbv
example : isPalindrome "xywyz" = false := by cbv
example : isPalindrome "xywxz" = false := by cbv
