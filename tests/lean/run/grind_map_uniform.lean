import Lean.Meta.Tactic.Grind
import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeMap
import Std.Data.TreeSet

#eval Lean.Meta.Grind.isEMatchTheorem `Std.DHashMap.isEmpty_emptyWithCapacity
#eval Lean.Meta.Grind.isEMatchTheorem `Std.HashMap.isEmpty_emptyWithCapacity
#eval Lean.Meta.Grind.isEMatchTheorem `Std.HashSet.isEmpty_emptyWithCapacity
#eval Lean.Meta.Grind.isEMatchTheorem `Std.TreeMap.isEmpty_emptyWithCapacity
#eval Lean.Meta.Grind.isEMatchTheorem `Std.TreeSet.isEmpty_emptyWithCapacity
