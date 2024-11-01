import Std.Time
import Init
open Std.Time

#eval do
  let res ← Database.defaultGetZoneRules "America/Sao_Paulo"
  if res.transitions.size < 1 then
    throw <| IO.userError "invalid quantity for America/Sao_Paulo"

#eval do
  let res ← Database.defaultGetLocalZoneRules
  if res.transitions.size < 1 then
    throw <| IO.userError "invalid quantity for the local timezone"
