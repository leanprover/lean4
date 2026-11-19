/-!
Generating the equations of a matcher with two discriminants and 64 alternatives with value
patterns. The catch-all equation is proved by traversing the tree of `dite (x = value) ..` nodes
once. It used to be proved with general purpose tactics whose cost at each node was proportional
to the number of alternatives, and equation generation needed more than 48000 heartbeats.
-/

set_option maxHeartbeats 25000

def twoDiscrs : String → Nat → Nat
  | "registered_name_0", 0 => 0
  | "registered_name_0", 1 => 1
  | "registered_name_1", 0 => 2
  | "registered_name_1", 1 => 3
  | "registered_name_2", 0 => 4
  | "registered_name_2", 1 => 5
  | "registered_name_3", 0 => 6
  | "registered_name_3", 1 => 7
  | "registered_name_4", 0 => 8
  | "registered_name_4", 1 => 9
  | "registered_name_5", 0 => 10
  | "registered_name_5", 1 => 11
  | "registered_name_6", 0 => 12
  | "registered_name_6", 1 => 13
  | "registered_name_7", 0 => 14
  | "registered_name_7", 1 => 15
  | "registered_name_8", 0 => 16
  | "registered_name_8", 1 => 17
  | "registered_name_9", 0 => 18
  | "registered_name_9", 1 => 19
  | "registered_name_10", 0 => 20
  | "registered_name_10", 1 => 21
  | "registered_name_11", 0 => 22
  | "registered_name_11", 1 => 23
  | "registered_name_12", 0 => 24
  | "registered_name_12", 1 => 25
  | "registered_name_13", 0 => 26
  | "registered_name_13", 1 => 27
  | "registered_name_14", 0 => 28
  | "registered_name_14", 1 => 29
  | "registered_name_15", 0 => 30
  | "registered_name_15", 1 => 31
  | "registered_name_16", 0 => 32
  | "registered_name_16", 1 => 33
  | "registered_name_17", 0 => 34
  | "registered_name_17", 1 => 35
  | "registered_name_18", 0 => 36
  | "registered_name_18", 1 => 37
  | "registered_name_19", 0 => 38
  | "registered_name_19", 1 => 39
  | "registered_name_20", 0 => 40
  | "registered_name_20", 1 => 41
  | "registered_name_21", 0 => 42
  | "registered_name_21", 1 => 43
  | "registered_name_22", 0 => 44
  | "registered_name_22", 1 => 45
  | "registered_name_23", 0 => 46
  | "registered_name_23", 1 => 47
  | "registered_name_24", 0 => 48
  | "registered_name_24", 1 => 49
  | "registered_name_25", 0 => 50
  | "registered_name_25", 1 => 51
  | "registered_name_26", 0 => 52
  | "registered_name_26", 1 => 53
  | "registered_name_27", 0 => 54
  | "registered_name_27", 1 => 55
  | "registered_name_28", 0 => 56
  | "registered_name_28", 1 => 57
  | "registered_name_29", 0 => 58
  | "registered_name_29", 1 => 59
  | "registered_name_30", 0 => 60
  | "registered_name_30", 1 => 61
  | "registered_name_31", 0 => 62
  | "registered_name_31", 1 => 63
  | _, _ => 1000

example := @twoDiscrs.match_1.eq_65
