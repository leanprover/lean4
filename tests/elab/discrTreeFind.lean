import Lean

/-!
Test basic lookup operations (match, match-liberal, and unify) on discrimination trees.
-/

open Lean Meta

opaque a : Nat
opaque b : Nat
opaque f : Nat → Nat
opaque h : Nat → Nat → Nat → Nat → Nat

/--
info: [0]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: [0, 2]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: [0, 2]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: [0, 2]
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: [0, 1, 4]
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b)))}"

/--
info: [0]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: [0]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: [0]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: [0]
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: [0, 1]
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  logInfo m!"{← t.getMatch (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))))}"

/--
info: [0]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: [0, 2]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: [0, 2]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: [0, 2]
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: [0, 1, 4]
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b)))}"

/--
info: [0, 1]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: [0, 1, 2]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: [0, 1, 2, 3]
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: [0, 1, 4, 2, 3]
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: [0, 1, 4]
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  logInfo m!"{← t.getUnify (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))))}"

/--
info: ([0, 1], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: ([0, 1, 2], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: ([0, 1, 2, 3], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: ([0, 1, 4, 2, 3], 1)
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: ([0, 1, 4, 2, 3], 1)
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkConst ``a))}\n${t}"
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b)))}"

/--
info: ([0, 1], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1]))))))
---
info: ([0, 1, 2], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2]))))
---
info: ([0, 1, 2, 3], 1)
$(f => (node (* => (node #[0])) (f => (node (* => (node #[1])))) (a => (node #[2])) (b => (node #[3]))))
---
info: ([0, 1, 4, 2, 3], 1)
$(f => (node
  (* => (node #[0]))
  (f => (node (* => (node #[1])) (b => (node #[4]))))
  (a => (node #[2]))
  (b => (node #[3]))))
---
info: ([0, 1, 4, 2, 3], 1)
-/
#guard_msgs in
#eval do
  let t : DiscrTree Nat := {}
  let t ← t.insert (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))) 0
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))) 1
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``a)) 2
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkConst ``b)) 3
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  let t ← t.insert (mkApp (mkConst ``f) (mkApp (mkConst ``f) (mkConst ``b))) 4
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat)))}\n${t}"
  logInfo m!"{← t.getMatchLiberal (mkApp (mkConst ``f) (mkApp (mkConst ``f) (← mkFreshExprMVar (mkConst ``Nat))))}"
