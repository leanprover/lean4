import Lean

/-! Exercise basic operations on discrimination trees -/

open Lean Meta

opaque f : Nat → Nat
opaque g : String → Nat
opaque h : Nat → Nat → Nat

/--
info: 1 | [([f, 1], 1)]
$(f => (node (1 => (node #[1]))))
---
info: 2 | [([f, 1], 1), ([f, 1], 2)]
$(f => (node (1 => (node #[1, 2]))))
---
info: 3 | [([f, 1], 1), ([f, 1], 2), ([f, 2], 3)]
$(f => (node (1 => (node #[1, 2])) (2 => (node #[3]))))
---
info: 4 | [([f, 1], 1), ([f, 1], 2), ([f, 2], 3), ([f, g, "a"], 4)]
$(f => (node (1 => (node #[1, 2])) (2 => (node #[3])) (g => (node ("a" => (node #[4]))))))
---
info: 5 | [([f, 1], 1), ([f, 1], 2), ([f, 2], 3), ([f, g, "a"], 4), ([f, h, 1, 2], 5)]
$(f => (node
  (1 => (node #[1, 2]))
  (2 => (node #[3]))
  (g => (node ("a" => (node #[4]))))
  (h => (node (1 => (node (2 => (node #[5]))))))))
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 1)) 1
  logInfo m!"{t.size} | {t.toArray}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 1)) 2
  logInfo m!"{t.size} | {t.toArray}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 2)) 3
  logInfo m!"{t.size} | {t.toArray}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``g) (mkStrLit "a"))) 4
  logInfo m!"{t.size} | {t.toArray}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkApp (mkConst ``h) (mkNatLit 1)) (mkNatLit 2))) 5
  logInfo m!"{t.size} | {t.toArray}\n${t}"

/--
info: (f => (node (10 => (node #[1, 2]))))
[([f, 10], 1), ([f, 10], 2)]
[1, 2] true true false
---
info: (f => (node (10 => (node #[2, 1]))))
[([f, 10], 2), ([f, 10], 1)]
[2, 1] true true false
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 1
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 2
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 2
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 1
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 2
  logInfo m!"{t}\n{t.toArray}\n{t.values} {t.containsValueP (· == 1)} {t.containsValueP (· == 2)} {t.containsValueP (· == 3)}"
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 2
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 10)) 1
  logInfo m!"{t}\n{t.toArray}\n{t.values} {t.containsValueP (· == 1)} {t.containsValueP (· == 2)} {t.containsValueP (· == 3)}"


/--
info: (f => (node
  (h => (node
    (0 => (node (0 => (node #[11])) (1 => (node #[12]))))
    (1 => (node (0 => (node #[13])) (1 => (node #[14]))))))))
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkApp (mkConst ``h) (mkNatLit 0)) (mkNatLit 0))) 1
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkApp (mkConst ``h) (mkNatLit 0)) (mkNatLit 1))) 2
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkApp (mkConst ``h) (mkNatLit 1)) (mkNatLit 0))) 3
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkApp (mkConst ``h) (mkNatLit 1)) (mkNatLit 1))) 4
  logInfo m!"{t.mapArrays (·.map (· + 10))}"

/--
info:
("A" => (node #[10, 11]))
("B" => (node #[12]))
(g => (node (0 => (node #[13, 14, 15]))))
(f => (node
  (0 => (node #[16]))
  (1 => (node #[17, 18]))
  (2 => (node #[19]))
  (f => (node (1 => (node #[20])) (2 => (node #[21]))))))
---
info:
("A" => (node #[0, 1]))
("B" => (node #[2]))
(g => (node (0 => (node #[3, 4, 5]))))
(f => (node (0 => (node #[6])) (1 => (node #[7, 8])) (2 => (node #[9])) (f => (node (1 => (node #[10]))))))
---
info:
("A" => (node #[0]))
("B" => (node #[2]))
(g => (node (0 => (node #[4]))))
(f => (node (0 => (node #[6])) (1 => (node #[8])) (f => (node (1 => (node #[10]))))))
---
info:
(g => (node (0 => (node #[3, 4, 5]))))
---
info:
("B" => (node #[2]))
(f => (node (0 => (node #[6])) (2 => (node #[9])) (f => (node (1 => (node #[10])) (2 => (node #[11]))))))
---
info: ("A" => (node #[0, 1])) (g => (node (0 => (node #[3, 4, 5])))) (f => (node (1 => (node #[7, 8]))))
---
info:
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkStrLit "A") 0
  let t ← t.insert (mkStrLit "A") 1
  let t ← t.insert (mkStrLit "B") 2
  let t ← t.insert (mkApp (mkConst ``g) (mkNatLit 0)) 3
  let t ← t.insert (mkApp (mkConst ``g) (mkNatLit 0)) 4
  let t ← t.insert (mkApp (mkConst ``g) (mkNatLit 0)) 5
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 0)) 6
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 1)) 7
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 1)) 8
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkNatLit 1))) 10
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkNatLit 2))) 11
  let t ← t.insert (mkApp (mkConst ``f) (mkNatLit 2)) 9
  logInfo m!"{t.mapArrays (·.map (· + 10))}"
  logInfo m!"{t.mapArrays (·.filter (· <= 10))}"
  logInfo m!"{t.mapArrays (·.filter (· % 2 = 0))}"
  logInfo m!"{t.mapArrays (fun arr => if arr.size > 2 then arr else #[])}"
  logInfo m!"{t.mapArrays (fun arr => if arr.size = 1 then arr else #[])}"
  logInfo m!"{t.mapArrays (fun arr => if arr.size = 1 then #[] else arr)}"
  logInfo m!"{t.mapArrays (β := String) (fun _ => #[])}"
