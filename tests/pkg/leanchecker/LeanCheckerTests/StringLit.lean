-- Test: string literal reduction needs `String.ofList` and `Char.ofNat`
--
-- The kernel unfolds string literals to `String.ofList [Char.ofNat n, ...]`, but `t1` does not
-- refer to these constants syntactically. `replay` must still add them before checking `t1`.

theorem t1 : "abc" ++ "def" = "abcdef" := by decide

theorem triv : True :=
  have _h : "abc" ++ "def" = "abcdef" := t1
  True.intro
