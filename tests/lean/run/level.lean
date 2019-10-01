import init.lean.level
open Lean

#eval Level.zero == Level.zero
#eval Level.zero == Level.succ Level.zero
#eval Level.max (Level.succ Level.zero) Level.zero == Level.succ Level.zero
#eval Level.max (Level.succ Level.zero) Level.zero == Level.max (Level.succ Level.zero) Level.zero
