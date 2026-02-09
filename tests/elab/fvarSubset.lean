import Lean

open Lean Meta
run_meta do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x =>
  withLocalDeclD `y nat fun y =>
  withLocalDeclD `z nat fun z =>
  withLocalDeclD `w nat fun w => do
    let o := mkNatLit 0
    let e1 ← mkAdd x x     -- x + x
    let e2 ← mkAdd x y     -- x + y
    let e3 ← mkAdd e2 z    -- (x + y) + z
    let e4 ← mkAdd e2 e2   -- (x + y) + (x + y)
    let e5 ← mkAdd e4 w    -- ((x + y) + (x + y)) + w
    let e6 ← mkAdd e5 z    -- (((x + y) + (x + y)) + w) + z
    assert! o.fvarsSubset e6
    assert! !e6.fvarsSubset o
    assert! o.fvarsSubset e1
    assert! !e1.fvarsSubset o
    assert! e1.fvarsSubset e1
    assert! e1.fvarsSubset e2
    assert! e6.fvarsSubset e6
    assert! !e2.fvarsSubset e1
    assert! e1.fvarsSubset e6
    assert! e4.fvarsSubset e6
    assert! !e3.fvarsSubset e5
    assert! !e5.fvarsSubset e3
    assert! e4.fvarsSubset e6
