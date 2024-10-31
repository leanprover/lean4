import Std.Time
import Init
open Std.Time

#eval do
  let res ← Database.defaultGetZoneRulesAt "America/Sao_Paulo"
  if res.transitions.size < 1 then
    throw <| IO.userError "invalid quantity for America/Sao_Paulo"
