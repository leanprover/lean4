-- String.reduceAppend
example : "hello" ++ " " ++ "world" = "hello world" := by simp
example : "" ++ "a" = "a" := by simp
example : "a" ++ "" = "a" := by simp
example : "" ++ "" = "" := by simp

-- String.reduceOfList
example : String.ofList ['a', 'b', 'c'] = "abc" := by simp
example : String.ofList [] = "" := by simp
example : String.ofList ['x'] = "x" := by simp

-- String.reduceToList
example : "abc".toList = ['a', 'b', 'c'] := by simp
example : "".toList = [] := by simp
example : "x".toList = ['x'] := by simp
example : "hello".toList = ['h', 'e', 'l', 'l', 'o'] := by simp

-- String.reducePush
example : "abc".push 'd' = "abcd" := by simp
example : "".push 'a' = "a" := by simp

-- String.reduceEq
example : "hello" = "hello" := by simp
example : "hello" = "foo" → False := by simp

-- String.reduceNe
example : "hello" ≠ "foo" := by simp

-- String.reduceBEq
example : ("hello" == "hello") = true := by simp
example : ("hello" == "foo") = false := by simp

-- String.reduceBNe
example : ("hello" != "foo") = true := by simp
example : ("hello" != "hello") = false := by simp

-- String.reduceLT
example : "abc" < "abd" := by simp
example : "a" < "b" := by simp

-- String.reduceLE
example : "abc" ≤ "abc" := by simp
example : "abc" ≤ "abd" := by simp

-- String.reduceGT
example : "abd" > "abc" := by simp
example : "b" > "a" := by simp

-- String.reduceGE
example : "abc" ≥ "abc" := by simp
example : "abd" ≥ "abc" := by simp

-- String.reduceSingleton
example : String.singleton ' ' = " " := by simp
example : String.singleton 'a' = "a" := by simp
example : String.singleton '\n' = "\n" := by simp

-- Combined: roundtrip toList/ofList
example : String.ofList "hello".toList = "hello" := by simp
