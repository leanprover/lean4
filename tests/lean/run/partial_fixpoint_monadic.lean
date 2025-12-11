/-!
Testing `partial_fixpoint` with monad transformers
-/

/-!
Using an `Option`-based monad
-/

abbrev M1 := ReaderT String (StateT String.Pos.Raw Option)

def parseAll1 (x : M1 α) : M1 (List α) := do
  if String.Pos.Raw.atEnd (← read) (← get) then
    return []
  let val ← x
  let list ← parseAll1 x
  return val :: list
partial_fixpoint

/--
info: equations:
theorem parseAll1.eq_1 : ∀ {α : Type} (x : M1 α),
  parseAll1 x = do
    let __do_lift ← read
    let __do_lift_1 ← get
    have __do_jp : PUnit → M1 (List α) := fun y => do
      let val ← x
      let list ← parseAll1 x
      pure (val :: list)
    if String.Pos.Raw.atEnd __do_lift __do_lift_1 = true then pure []
      else do
        let y ← pure PUnit.unit
        __do_jp y
-/
#guard_msgs in #print equations parseAll1

/-!
Using an `IO`-based monad
-/

abbrev M2 := ReaderT String (StateRefT String.Pos.Raw IO)

def parseAll2 (x : M2 α) : M2 (List α) := do
  if String.Pos.Raw.atEnd (← read) (← get) then
    return []
  let val ← x
  let list ← parseAll2 x
  return val :: list
partial_fixpoint

/--
info: equations:
theorem parseAll2.eq_1 : ∀ {α : Type} (x : M2 α),
  parseAll2 x = do
    let __do_lift ← read
    let __do_lift_1 ← get
    have __do_jp : PUnit → M2 (List α) := fun y => do
      let val ← x
      let list ← parseAll2 x
      pure (val :: list)
    if String.Pos.Raw.atEnd __do_lift __do_lift_1 = true then pure []
      else do
        let y ← pure PUnit.unit
        __do_jp y
-/
#guard_msgs in #print equations parseAll2
