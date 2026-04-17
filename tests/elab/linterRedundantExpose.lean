module

/-! `warn.redundantExpose` tests -/

public section

-- `@[expose]` on abbrev should warn
/-- warning: `@[expose]` has no effect; this declaration would be exposed by default -/
#guard_msgs in
@[expose] abbrev myAbbrev := 1

-- `@[expose]` on a regular public def should not warn
@[expose] def myDef := 1

-- `@[no_expose]` on a regular def outside expose section should warn
/-- warning: `@[no_expose]` has no effect; this declaration would not be exposed by default -/
#guard_msgs in
@[no_expose] def myDef3 := 3

-- `@[expose]` on a data instance should warn
/-- warning: `@[expose]` has no effect; this declaration would be exposed by default -/
#guard_msgs in
@[expose] instance : Inhabited Nat := ⟨0⟩

-- `@[expose]` on a Prop instance should not warn
@[expose] instance : Nonempty Nat := ⟨0⟩

-- `@[no_expose]` on abbrev should not warn (it overrides auto-expose)
@[no_expose] abbrev myAbbrev2 := 5

-- `@[no_expose]` on a data instance should not warn (it overrides auto-expose)
@[no_expose] instance : Inhabited Bool := ⟨false⟩

end

-- `@[expose]` inside `@[expose] section` on a def should warn
@[expose] public section
/-- warning: `@[expose]` has no effect; this declaration would be exposed by default -/
#guard_msgs in
@[expose] def myDef2 := 2

-- `@[no_expose]` inside `@[expose] section` should not warn (it's meaningful)
@[no_expose] def myDef4 := 4
end

-- disabling the linter should suppress warnings
public section
set_option warn.redundantExpose false in
@[expose] abbrev myAbbrev3 := 6
end
