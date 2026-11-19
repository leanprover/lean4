import Lean

/-!
Tests how the cost of `do` elaboration grows with the size of the `do` block. Every family of `do`
blocks is elaborated at sizes `n`, `2n` and `4n`, with heartbeat counts `h₁`, `h₂` and `h₄`. For
`d₁ = h₂ - h₁` and `d₂ = h₄ - h₂`, a cost linear in the size gives `d₂ / d₁ = 2`, and a quadratic
cost gives `d₂ / d₁ = 4`. Every family has an upper bound for `d₂ / d₁`. The bound is `2.5` for the
families of linear cost, and slightly above the measured ratio for the other families.
-/

open Lean Elab Command

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def g (x : Nat) : StateM Nat Nat := pure (x + 1)

def gOpt (i : Nat) : StateM Nat (Option Nat) := pure (some i)

def a : StateM Nat Nat := get

def vars (m : Nat) : Array Ident := (Array.range m).map fun j => mkIdent (.mkSimple s!"x{j}")

def sumOf (xs : Array Ident) : CommandElabM Term :=
  (xs.extract 1).foldlM (init := (xs[0]! : Term)) fun t x => `($t + $x)

/-- `n` nested levels `match (← do let a ← gOpt i; pure a) with | .some r => pure r | none => (do …)`. -/
def nestedMatchBind (name : Ident) (n : Nat) : CommandElabM Command := do
  let mut body : DoSeq ← `(doSeq| pure 0)
  for i in (List.range n).reverse do
    body ← `(doSeq| match (← do let a ← gOpt $(quote i); pure a) with
                    | .some r => pure r
                    | none => (do $body))
  `(noncomputable def $name : StateM Nat Nat := do $body)

/-- `n` reassignments `xᵢ ← g xᵢ` over 10 `let mut` variables. -/
def reassignSeq (name : Ident) (n : Nat) : CommandElabM Command := do
  let xs := vars 10
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x := 0)
  let steps ← (Array.range n).mapM fun i =>
    let x := xs[i % 10]!
    `(Parser.Term.doSeqItem| $x:ident ← g $x)
  let sum ← sumOf xs
  `(noncomputable def $name : StateM Nat Nat := do
    $decls*
    $steps*
    pure $sum)

/-- `let r := (← g (← g (… (← g 0))))` with `n` nested actions. -/
def deepActions (name : Ident) (n : Nat) : CommandElabM Command := do
  let zero ← `(0)
  let t ← (Array.range n).foldlM (init := zero) fun t _ => `((← g $t))
  `(noncomputable def $name : StateM Nat Nat := do
    let r := $t
    pure r)

/-- `let r := (← a) + … + (← a)` with `n` actions side by side. -/
def flatActions (name : Ident) (n : Nat) : CommandElabM Command := do
  let first ← `((← a))
  let t ← (Array.range (n - 1)).foldlM (init := first) fun t _ => `($t + (← a))
  `(noncomputable def $name : StateM Nat Nat := do
    let r := $t
    pure r)

/-- `n` statements `if b i then xⱼ := xⱼ + i` over 20 `let mut` variables, typed or untyped. -/
def ifSeq (typed : Bool) (name : Ident) (n : Nat) : CommandElabM Command := do
  let xs := vars 20
  let decls ← xs.mapM fun x =>
    if typed then `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
    else `(Parser.Term.doSeqItem| let mut $x := 0)
  let ifs ← (Array.range n).mapM fun i =>
    let x := xs[i % 20]!
    `(Parser.Term.doSeqItem| if b $(quote i) then $x:ident := $x + $(quote i))
  let sum ← sumOf xs
  `(noncomputable def $name (b : Nat → Bool) : StateM Nat Nat := do
    $decls*
    $ifs*
    pure $sum)

/-- `n` nested levels `if b i then acc := acc + i; …`, each followed by `acc := acc * (i + 2)`. -/
def nestedIf (name : Ident) (n : Nat) : CommandElabM Command := do
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) :=
    #[← `(Parser.Term.doSeqItem| $acc:ident := 0)]
  for i in (List.range n).reverse do
    inner := #[← `(Parser.Term.doSeqItem| if b $(quote i) then
                    $acc:ident := $acc + $(quote i)
                    $inner*),
               ← `(Parser.Term.doSeqItem| $acc:ident := $acc * $(quote (i + 2)))]
  `(noncomputable def $name (b : Nat → Bool) : StateM Nat Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc)

/-- `n` pairs `let pᵢ ← pure ⟨i, i⟩; let _qᵢ : Nat × Nat := pᵢ`, where every `pᵢ` postpones. -/
def postpone (name : Ident) (n : Nat) : CommandElabM Command := do
  let ps := (Array.range n).map fun i => mkIdent (.mkSimple s!"p{i}")
  let items ← (Array.range n).foldlM (init := #[]) fun items i => do
    let p := ps[i]!
    let q := mkIdent (.mkSimple s!"_q{i}")
    return items.push (← `(Parser.Term.doSeqItem| let $p:ident ← pure ⟨$(quote i), $(quote i)⟩))
      |>.push (← `(Parser.Term.doSeqItem| let $q:ident : Nat × Nat := $p))
  `(noncomputable def $name : StateM Nat (Nat × Nat) := do
    $items*
    pure $(ps.back!))

/-- `n` nested `try … catch … finally` levels in `ExceptT String (StateM Nat)`. -/
def nestedTry (name : Ident) (n : Nat) : CommandElabM Command := do
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) := #[]
  for i in (List.range n).reverse do
    inner := #[← `(Parser.Term.doSeqItem| try
                    $acc:ident := $acc + $(quote i)
                    if $acc > $(quote i) then throw "e"
                    $inner*
                    $acc:ident := $acc + 1
                  catch _ =>
                    $acc:ident := $acc * 2
                  finally
                    modify (· + 1))]
  `(noncomputable def $name : ExceptT String (StateM Nat) Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc)

/-- `n` nested `for` loops whose bodies `continue`, `break`, `return` and reassign `acc`. -/
def nestedFor (name : Ident) (n : Nat) : CommandElabM Command := do
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) := #[]
  for i in (List.range n).reverse do
    let y := mkIdent (.mkSimple s!"y{i}")
    inner := #[← `(Parser.Term.doSeqItem| for $y:ident in xs do
                    if $y = $(quote i) then continue
                    if $y = $(quote (i + 1)) then break
                    if $acc > $(quote (1000 + i)) then return $acc
                    $acc:ident := $acc + $y
                    $inner*)]
  `(noncomputable def $name (xs : List Nat) : StateM Nat Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc)

/-- One `for` loop that reassigns `n` `let mut` variables. -/
def manyMut (name : Ident) (n : Nat) : CommandElabM Command := do
  let xs := vars n
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let body ← xs.mapM fun x => `(Parser.Term.doSeqItem| $x:ident := $x + y)
  let sum ← sumOf xs
  `(noncomputable def $name (ys : List Nat) : StateM Nat Nat := do
    $decls*
    for y in ys do
      $body*
    pure $sum)

/-- One `match k with` of `n` arms, each reassigning one of 4 `let mut` variables. -/
def arms (name : Ident) (n : Nat) : CommandElabM Command := do
  let xs := vars 4
  let x0 := xs[0]!
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let rhss ← (Array.range n).mapM fun i =>
    let x := xs[i % 4]!
    `(doSeq| $x:ident := $(quote i))
  let pats ← (Array.range n).mapM fun i => `($(quote i))
  let sum ← sumOf xs
  `(noncomputable def $name (k : Nat) : StateM Nat Nat := do
    $decls*
    match k with
    $[| $pats:term => $rhss:doSeq]*
    | _ => $x0:ident := 1
    pure $sum)

/-- One `if … else if …` chain of `n` branches, each reassigning one of 4 `let mut` variables. -/
def elseIfs (name : Ident) (n : Nat) : CommandElabM Command := do
  let xs := vars 4
  let x0 := xs[0]!
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let rhss ← (Array.range n).mapM fun i =>
    let x := xs[i % 4]!
    `(doSeq| $x:ident := $(quote i))
  let conds ← (Array.range n).mapM fun i => `(Parser.Term.doIfCond| k = $(quote i))
  let sum ← sumOf xs
  `(noncomputable def $name (k : Nat) : StateM Nat Nat := do
    $decls*
    if k = $(quote n) then $x0:ident := 0
    $[else if $conds:doIfCond then $rhss]*
    else $x0:ident := 1
    pure $sum)

def heartbeatsOf (mk : Ident → Nat → CommandElabM Command) (tag : String) (n : Nat) :
    CommandElabM Nat := do
  let cmd ← mk (mkIdent (.mkSimple s!"{tag}_{n}")) n
  let start ← IO.getNumHeartbeats
  elabCommand cmd
  return (← IO.getNumHeartbeats) - start

/--
Elaborates the family `mk` at sizes `n`, `2n` and `4n` and throws unless `d₂ / d₁ ≤ bound`.
A run at size `n / 4` fills the caches first.
-/
def checkScaling (tag : String) (mk : Ident → Nat → CommandElabM Command) (n : Nat)
    (bound : Float) : CommandElabM Unit := do
  discard <| heartbeatsOf mk s!"{tag}_warm" (max 1 (n / 4))
  let h₁ ← heartbeatsOf mk tag n
  let h₂ ← heartbeatsOf mk tag (2 * n)
  let h₄ ← heartbeatsOf mk tag (4 * n)
  let ratio := (h₄ - h₂).toFloat / (h₂ - h₁).toFloat
  unless ratio ≤ bound do
    throwError "`{tag}`: heartbeats {h₁}, {h₂}, {h₄} at sizes {n}, {2 * n}, {4 * n} give \
      d₂ / d₁ = {ratio}, above the bound {bound}"

run_cmd do
  checkScaling "nestedMatchBind" nestedMatchBind 50 2.5
  checkScaling "reassignSeq" reassignSeq 100 2.5
  checkScaling "deepActions" deepActions 100 2.5
  checkScaling "flatActions" flatActions 50 3.0
  checkScaling "ifSeqTyped" (ifSeq true) 50 3.4
  checkScaling "ifSeqUntyped" (ifSeq false) 10 4.2
  checkScaling "nestedIf" nestedIf 20 3.1
  checkScaling "postpone" postpone 10 6.0
  checkScaling "nestedTry" nestedTry 4 3.3
  checkScaling "nestedFor" nestedFor 6 2.9
  checkScaling "manyMut" manyMut 20 3.3
  checkScaling "arms" arms 50 3.2
  checkScaling "elseIfs" elseIfs 50 3.1
