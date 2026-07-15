import Std

example : ("hello world".split (· == ' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

example : ("hello world".split (· = ' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

example : ("hello world".split (' ')).toList.map (·.toString) = ["hello", "world"] := by cbv

def numbers : List String :=
  ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def numberToNumber : Std.HashMap String Nat :=
  (0...=9).iter.fold (init := ∅) (fun sofar num => sofar.insert numbers[num]! num)

def sortNumbers (str : String) : String :=
  str.split ' '
    |>.filter (!·.isEmpty)
    |>.map (numberToNumber[·.copy]!)
    |>.toList
    |>.mergeSort
    |>.map (numbers[·]!)
    |> String.intercalate " "

example : sortNumbers "" = "" := by cbv
example : sortNumbers "three" = "three" := by cbv
example : sortNumbers "three five" = "three five" := by cbv
example : sortNumbers "five three" = "three five" := by cbv
example : sortNumbers "one one" = "one one" := by cbv
example : sortNumbers "six one two" = "one two six" := by cbv
