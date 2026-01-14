import Lean.Data.Json.Elab

/-- info: {"lookACalc": 131,
 "lemonCount": 100000000000000000000000000000000,
 "isCool": true,
 "isBug": null,
 "hello": "world",
 "cheese": ["edam", "cheddar", {"rank": 100.2, "kind": "spicy"}]}-/
#guard_msgs in
#eval json% {
  hello : "world",
  cheese : ["edam", "cheddar", {kind : "spicy", rank : 100.2}],
  lemonCount : 100e30,
  isCool : true,
  isBug : null,
  lookACalc: $(23 + 54 * 2)
}

-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/json.20elaborator
example : Lean.Json := Id.run do
  let _x := true
  return json% {"x" : 1}
