import Lean.Data.Json
open Lean

deriving instance BEq for Except

example : Json.parse "\"\\u7406\\u79d1\"" == .ok "理科" := by native_decide
example : Json.parse "\"\\u7406\\u79D1\"" == .ok "理科" := by native_decide

example : Json.pretty "\x0b" == "\"\\u000b\"" := by native_decide
example : Json.pretty "\x1b" == "\"\\u001b\"" := by native_decide
example : Json.parse "\"\\u000b\"" == .ok "\x0b" := by native_decide
example : Json.parse "\"\\u001b\"" == .ok "\x1b" := by native_decide
example : Json.parse "\"\\u000B\"" == .ok "\x0b" := by native_decide
example : Json.parse "\"\\u001B\"" == .ok "\x1b" := by native_decide
