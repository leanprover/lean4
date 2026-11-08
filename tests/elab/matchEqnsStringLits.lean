/-!
Generating the equation lemmas of a definition by `match` on many `String` literals. With 64
alternatives, generation used to hit the heartbeat limit (#16313).
-/

def onStr : String → Nat
  | "registered_name_0" => 0
  | "registered_name_1" => 1
  | "registered_name_2" => 2
  | "registered_name_3" => 3
  | "registered_name_4" => 4
  | "registered_name_5" => 5
  | "registered_name_6" => 6
  | "registered_name_7" => 7
  | "registered_name_8" => 8
  | "registered_name_9" => 9
  | "registered_name_10" => 10
  | "registered_name_11" => 11
  | "registered_name_12" => 12
  | "registered_name_13" => 13
  | "registered_name_14" => 14
  | "registered_name_15" => 15
  | "registered_name_16" => 16
  | "registered_name_17" => 17
  | "registered_name_18" => 18
  | "registered_name_19" => 19
  | "registered_name_20" => 20
  | "registered_name_21" => 21
  | "registered_name_22" => 22
  | "registered_name_23" => 23
  | "registered_name_24" => 24
  | "registered_name_25" => 25
  | "registered_name_26" => 26
  | "registered_name_27" => 27
  | "registered_name_28" => 28
  | "registered_name_29" => 29
  | "registered_name_30" => 30
  | "registered_name_31" => 31
  | "registered_name_32" => 32
  | "registered_name_33" => 33
  | "registered_name_34" => 34
  | "registered_name_35" => 35
  | "registered_name_36" => 36
  | "registered_name_37" => 37
  | "registered_name_38" => 38
  | "registered_name_39" => 39
  | "registered_name_40" => 40
  | "registered_name_41" => 41
  | "registered_name_42" => 42
  | "registered_name_43" => 43
  | "registered_name_44" => 44
  | "registered_name_45" => 45
  | "registered_name_46" => 46
  | "registered_name_47" => 47
  | "registered_name_48" => 48
  | "registered_name_49" => 49
  | "registered_name_50" => 50
  | "registered_name_51" => 51
  | "registered_name_52" => 52
  | "registered_name_53" => 53
  | "registered_name_54" => 54
  | "registered_name_55" => 55
  | "registered_name_56" => 56
  | "registered_name_57" => 57
  | "registered_name_58" => 58
  | "registered_name_59" => 59
  | "registered_name_60" => 60
  | "registered_name_61" => 61
  | "registered_name_62" => 62
  | "registered_name_63" => 63
  | _ => 1000

example := @onStr.match_1.eq_65
example := @onStr.eq_65
