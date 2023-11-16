import Lean

-- Coordinates in a two dimensional grid. ⟨0,0⟩ is the upper left.
structure Coords where
  x : Nat -- column number
  y : Nat -- row number
deriving BEq

instance : ToString Coords where
  toString := (λ ⟨x,y⟩ => String.join ["Coords.mk ", toString x, ", ", toString y])

structure GameState where
  size     : Coords      -- coordinates of bottom-right cell
  position : Coords      -- row and column of the player
  walls    : List Coords -- maze cells that are not traversible

-- We define custom syntax for GameState.

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence
declare_syntax_cat game_row
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row

syntax "─" : horizontal_border

syntax "\n┌" horizontal_border* "┐\n" : game_top_row

syntax "└" horizontal_border* "┘\n" : game_bottom_row

syntax "░" : game_cell -- empty
syntax "▓" : game_cell -- wall
syntax "@" : game_cell -- player

syntax "│" game_cell* "│\n" : game_row

syntax:max game_top_row game_row* game_bottom_row : term

inductive CellContents where
  | empty  : CellContents
  | wall   : CellContents
  | player : CellContents

def update_state_with_row_aux : Nat → Nat → List CellContents → GameState → GameState
| currentRowNum, currentColNum, [], oldState => oldState
| currentRowNum, currentColNum, cell::contents, oldState =>
    let oldState' := update_state_with_row_aux currentRowNum (currentColNum+1) contents oldState
    match cell with
    | CellContents.empty => oldState'
    | CellContents.wall => {oldState' .. with
                            walls := ⟨currentColNum,currentRowNum⟩::oldState'.walls}
    | CellContents.player => {oldState' .. with
                              position := ⟨currentColNum,currentRowNum⟩}

def update_state_with_row : Nat → List CellContents → GameState → GameState
| currentRowNum, rowContents, oldState => update_state_with_row_aux currentRowNum 0 rowContents oldState

-- size, current row, remaining cells -> gamestate
def game_state_from_cells_aux : Coords → Nat → List (List CellContents) → GameState
| size, _, [] => ⟨size, ⟨0,0⟩, []⟩
| size, currentRow, row::rows =>
        let prevState := game_state_from_cells_aux size (currentRow + 1) rows
        update_state_with_row currentRow row prevState

-- size, remaining cells -> gamestate
def game_state_from_cells : Coords → List (List CellContents) → GameState
| size, cells => game_state_from_cells_aux size 0 cells

def termOfCell : Lean.TSyntax `game_cell → Lean.MacroM (Lean.TSyntax `term)
| `(game_cell| ░) => `(CellContents.empty)
| `(game_cell| ▓) => `(CellContents.wall)
| `(game_cell| @) => `(CellContents.player)
| _ => Lean.Macro.throwError "unknown game cell"

def termOfGameRow : Nat → Lean.TSyntax `game_row → Lean.MacroM (Lean.TSyntax `term)
| expectedRowSize, `(game_row| │$cells:game_cell*│) =>
      do if cells.size != expectedRowSize
         then Lean.Macro.throwError "row has wrong size"
         let cells' ← Array.mapM termOfCell cells
         `([$cells',*])
| _, _ => Lean.Macro.throwError "unknown game row"

macro_rules
| `(┌ $tb:horizontal_border* ┐
    $rows:game_row*
    └ $bb:horizontal_border* ┘) =>
      do let rsize := Lean.Syntax.mkNumLit (toString rows.size)
         let csize := Lean.Syntax.mkNumLit (toString tb.size)
         if tb.size != bb.size then Lean.Macro.throwError "top/bottom border mismatch"
         let rows' ← Array.mapM (termOfGameRow tb.size) rows
         `(game_state_from_cells ⟨$csize,$rsize⟩ [$rows',*])

---------------------------
-- Now we define a delaborator that will cause GameState to be rendered as a maze.

def extractXY : Lean.Expr → Lean.MetaM Coords
| e => do
  let e':Lean.Expr ← (Lean.Meta.whnf e)
  let sizeArgs := Lean.Expr.getAppArgs e'
  let x ← Lean.Meta.whnf sizeArgs[0]!
  let y ← Lean.Meta.whnf sizeArgs[1]!
  let numCols := (Lean.Expr.natLit? x).get!
  let numRows := (Lean.Expr.natLit? y).get!
  return Coords.mk numCols numRows

partial def extractWallList : Lean.Expr → Lean.MetaM (List Coords)
| exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  if f.constName!.toString == "List.cons"
  then let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractWallList consArgs[2]!
       let ⟨wallCol, wallRow⟩ ← extractXY consArgs[1]!
       return (Coords.mk wallCol wallRow) :: rest
  else return [] -- "List.nil"

partial def extractGameState : Lean.Expr → Lean.MetaM GameState
| exp => do
    let exp': Lean.Expr ← (Lean.Meta.whnf exp)
    let gameStateArgs := Lean.Expr.getAppArgs exp'
    let size ← extractXY gameStateArgs[0]!
    let playerCoords ← extractXY gameStateArgs[1]!
    let walls ← extractWallList gameStateArgs[2]!
    pure ⟨size, playerCoords, walls⟩

def update2dArray {α : Type} : Array (Array α) → Coords → α → Array (Array α)
| a, ⟨x,y⟩, v =>
   Array.set! a y $ Array.set! (Array.get! a y) x v

def update2dArrayMulti {α : Type} : Array (Array α) → List Coords → α → Array (Array α)
| a, [], _ => a
| a, c::cs, v =>
     let a' := update2dArrayMulti a cs v
     update2dArray a' c v

def delabGameRow : Array (Lean.TSyntax `game_cell) → Lean.PrettyPrinter.Delaborator.DelabM (Lean.TSyntax `game_row)
| a => `(game_row| │ $a:game_cell* │)

def delabGameState : Lean.Expr → Lean.PrettyPrinter.Delaborator.Delab
| e =>
  do guard $ e.getAppNumArgs == 3
     let ⟨⟨numCols, numRows⟩, playerCoords, walls⟩ ←
       try extractGameState e
       catch err => failure -- can happen if game state has variables in it

     let topBar := Array.mkArray numCols $ ← `(horizontal_border| ─)
     let emptyCell ← `(game_cell| ░)
     let emptyRow := Array.mkArray numCols emptyCell
     let emptyRowStx ← `(game_row| │$emptyRow:game_cell*│)
     let allRows := Array.mkArray numRows emptyRowStx

     let a0 := Array.mkArray numRows $ Array.mkArray numCols emptyCell
     let a1 := update2dArray a0 playerCoords $ ← `(game_cell| @)
     let a2 := update2dArrayMulti a1 walls $ ← `(game_cell| ▓)
     let aa ← Array.mapM delabGameRow a2

     `(┌$topBar:horizontal_border*┐
       $aa:game_row*
       └$topBar:horizontal_border*┘)

-- The attribute [delab] registers this function as a delaborator for the GameState.mk constructor.
@[delab app.GameState.mk] def delabGameStateMk : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
  delabGameState e

-- We register the same elaborator for applications of the game_state_from_cells function.
@[delab app.game_state_from_cells] def delabGameState' : Lean.PrettyPrinter.Delaborator.Delab :=
  do let e ← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr
     let e' ← (Lean.Meta.whnf e)
     delabGameState e'

--------------------------

inductive Move where
  | east  : Move
  | west  : Move
  | north : Move
  | south : Move

@[simp]
def make_move : GameState → Move → GameState
| ⟨s, ⟨x,y⟩, w⟩, Move.east =>
             if w.notElem ⟨x+1, y⟩ ∧ x + 1 ≤ s.x
             then ⟨s, ⟨x+1, y⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.west =>
             if w.notElem ⟨x-1, y⟩
             then ⟨s, ⟨x-1, y⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.north =>
             if w.notElem ⟨x, y-1⟩
             then ⟨s, ⟨x, y-1⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.south =>
             if w.notElem ⟨x, y + 1⟩ ∧ y + 1 ≤ s.y
             then ⟨s, ⟨x, y+1⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩

def is_win : GameState → Prop
| ⟨⟨sx, sy⟩, ⟨x,y⟩, w⟩ => x = 0 ∨ y = 0 ∨ x + 1 = sx ∨ y + 1 = sy

def can_escape (state : GameState) : Prop :=
  ∃ (gs : List Move), is_win (List.foldl make_move state gs)

theorem can_still_escape (g : GameState) (m : Move) (hg : can_escape (make_move g m)) : can_escape g :=
 have ⟨pms, hpms⟩ := hg
 Exists.intro (m::pms) hpms

theorem step_west
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y⟩)
  (W : can_escape ⟨s,⟨x,y⟩,w⟩) :
  can_escape ⟨s,⟨x+1,y⟩,w⟩ :=
   by have hmm : GameState.mk s ⟨x,y⟩ w = make_move ⟨s,⟨x+1, y⟩,w⟩ Move.west :=
               by have h' : x + 1 - 1 = x := rfl
                  simp [h', hclear']
      rw [hmm] at W
      exact can_still_escape ⟨s,⟨x+1,y⟩,w⟩ Move.west W

theorem step_east
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x+1,y⟩)
  (hinbounds : x + 1 ≤ s.x)
  (E : can_escape ⟨s,⟨x+1,y⟩,w⟩) :
  can_escape ⟨s,⟨x, y⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x+1,y⟩ w = make_move ⟨s, ⟨x,y⟩,w⟩ Move.east :=
         by simp [hclear', hinbounds]
       rw [hmm] at E
       exact can_still_escape ⟨s, ⟨x,y⟩, w⟩ Move.east E

theorem step_north
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y⟩)
  (N : can_escape ⟨s,⟨x,y⟩,w⟩) :
  can_escape ⟨s,⟨x, y+1⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x,y⟩ w = make_move ⟨s,⟨x, y+1⟩,w⟩ Move.north :=
         by have h' : y + 1 - 1 = y := rfl
            simp [h', hclear']
       rw [hmm] at N
       exact can_still_escape ⟨s,⟨x,y+1⟩,w⟩ Move.north N

theorem step_south
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y+1⟩)
  (hinbounds : y + 1 ≤ s.y)
  (S : can_escape ⟨s,⟨x,y+1⟩,w⟩) :
  can_escape ⟨s,⟨x, y⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x,y+1⟩ w = make_move ⟨s,⟨x, y⟩,w⟩ Move.south :=
            by simp [hclear', hinbounds]
       rw [hmm] at S
       exact can_still_escape ⟨s,⟨x,y⟩,w⟩ Move.south S

def escape_west {sx sy : Nat} {y : Nat} {w : List Coords} : can_escape ⟨⟨sx, sy⟩,⟨0, y⟩,w⟩ :=
    ⟨[], Or.inl rfl⟩

def escape_east {sy x y : Nat} {w : List Coords} : can_escape ⟨⟨x+1, sy⟩,⟨x, y⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inr $ Or.inl rfl⟩

def escape_north {sx sy : Nat} {x : Nat} {w : List Coords} : can_escape ⟨⟨sx, sy⟩,⟨x, 0⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inl rfl⟩

def escape_south {sx x y : Nat} {w: List Coords} : can_escape ⟨⟨sx, y+1⟩,⟨x, y⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inr $ Or.inr rfl⟩

-- Define an "or" tactic combinator, like <|> in Lean 3.
elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   try Lean.Elab.Tactic.evalTactic t1
   catch err => Lean.Elab.Tactic.evalTactic t2

elab "fail" m:term  : tactic => throwError m

macro "out" : tactic => `(tactic|
  apply escape_north ⟨|⟩ apply escape_south ⟨|⟩
  apply escape_east ⟨|⟩ apply escape_west ⟨|⟩
  fail "not currently at maze boundary")

def maze1 := ┌───┐
             │▓▓▓│
             │░@▓│
             │▓▓▓│
             └───┘

def foo : can_escape maze1 := by
  apply step_west
  set_option trace.Meta.debug true in
  simp (config := { decide := true })
  out
