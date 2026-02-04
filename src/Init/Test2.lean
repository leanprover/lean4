module

prelude
public import Init.NotationExtra

public class UpwardEnumerable (α : Type u) where
  succMany? (n : Nat) (a : α) : Option α

public instance inst : UpwardEnumerable Int8 where
  succMany? _ i := some i

theorem instUpwardEnumerable_eq :
    inst.succMany? n x = some x := by
  simp only [inst]

/-- error: `simp` made no progress -/
#guard_msgs in
theorem instUpwardEnumerable_eq' :
    inst.succMany? n x = y := by
  simp only
