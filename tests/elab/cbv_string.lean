import Std

-- String append
theorem testAppend : "abc" ++ "def" = "abcdef" := by cbv

/--
info: theorem testAppend : "abc" ++ "def" = "abcdef" :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl "abcdef")) "abcdef") (eq_self "abcdef"))
-/
#guard_msgs in
#print testAppend

-- String push
theorem testPush : String.push "abc" 'd' = "abcd" := by cbv

/--
info: theorem testPush : "abc".push 'd' = "abcd" :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl "abcd")) "abcd") (eq_self "abcd"))
-/
#guard_msgs in
#print testPush

-- String singleton
theorem testSingleton : String.singleton 'a' = "a" := by cbv

/--
info: theorem testSingleton : String.singleton 'a' = "a" :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl "a")) "a") (eq_self "a"))
-/
#guard_msgs in
#print testSingleton

-- String.ofList
theorem testOfList : String.ofList ['a', 'b', 'c'] = "abc" := by cbv

/--
info: theorem testOfList : String.ofList ['a', 'b', 'c'] = "abc" :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl "abc")) "abc") (eq_self "abc"))
-/
#guard_msgs in
#print testOfList

-- String.toList
theorem testToList : String.toList "abc" = ['a', 'b', 'c'] := by cbv

/--
info: theorem testToList : "abc".toList = ['a', 'b', 'c'] :=
of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.refl ['a', 'b', 'c'])) ['a', 'b', 'c']) (eq_self ['a', 'b', 'c']))
-/
#guard_msgs in
#print testToList

-- Empty string operations
theorem testAppendEmpty : "" ++ "" = "" := by cbv

theorem testOfListEmpty : String.ofList [] = "" := by cbv

theorem testToListEmpty : String.toList "" = [] := by cbv
