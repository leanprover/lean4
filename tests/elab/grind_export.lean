import Lean
import Std

open Lean Meta Elab Grind

namespace Experiment

inductive NameFilter where
  | contains (s : String)
  | startsWith (s : String)
  | endsWith (s : String)
  | inModule (m : Name)
  | and (l r : NameFilter)
  | or (l r : NameFilter)
  | compl (f : NameFilter)


declare_syntax_cat filter

syntax "{" term "}" : filter
syntax filter " ∧ " filter : filter
syntax filter " ∨ " filter : filter
syntax "(" filter ")" : filter
syntax "¬" filter : filter

syntax "[filter|" filter "]" : term


macro_rules
  | `([filter| { $t:term }]) => `(($t : NameFilter))
  | `([filter| $lhs ∧ $rhs ]) => `(NameFilter.and [filter| $lhs] [filter| $rhs])
  | `([filter| $lhs ∨ $rhs ]) => `(NameFilter.or [filter| $lhs] [filter| $rhs])
  | `([filter| ¬ $f ]) => `(NameFilter.compl [filter| $f])
  | `([filter| ($f) ]) => `([filter| $f])

def NameFilter.eval (f : NameFilter) (const : Name) : CoreM Bool := do
  let constStr := const.toString
  let some moduleIdx := (← getEnv).const2ModIdx[const]? | return false
  let some module := (← getEnv).allImportedModuleNames[moduleIdx]? | return false
  return go f constStr module
where
  go (f : NameFilter) (constStr : String) (module : Name) : Bool :=
    match f with
    | .contains s => constStr.contains s
    | .startsWith s => constStr.startsWith s
    | .endsWith s => constStr.endsWith s
    | .inModule m => module == m
    | .and l r => go l constStr module && go r constStr module
    | .or l r => go l constStr module || go r constStr module
    | .compl f => !(go f constStr module)



structure Graph where
  edges : Std.HashMap Name (Std.HashMap Name Nat) := {}

instance : ToJson Graph where
  toJson g := toJson <| g.edges.toArray |>.map fun (k, v) => (k, v.toArray)

def Graph.merge (g1 g2 : Graph) : Graph := Id.run do
  let mut (⟨source⟩, ⟨target⟩) := if g1.edges.size > g2.edges.size then (g2, g1) else (g1, g2)
  for (src, dsts) in source do
    target := target.alter src fun
      | none => some <| dsts
      | some tdsts => Id.run do
        let mut tdsts := tdsts
        for (dst, weight) in dsts do
          tdsts := tdsts.alter dst fun
            | none => some 1
            | some weight' => some <| weight + weight'
        return some tdsts
  return ⟨target⟩

def Graph.addEdge (g : Graph) (src dst : Name) : Graph :=
  if src == dst then
    g
  else
    let ⟨edges⟩ := g
    let edges := edges.alter src fun
      | none => some {(dst, 1)}
      | some dsts => some <| dsts.alter dst fun
        | none => some 1
        | some weight => some <| weight + 1
    ⟨edges⟩

def getSuccessors (const : Name) : MetaM Graph := do
  let info ← getConstInfo const
  let type := info.type
  let mvarId ← forallTelescope type fun _ type => do
    withLocalDeclD `h type fun _ => do
      return (← mkFreshExprMVar (mkConst ``False)).mvarId!
  let config := {}
  let params ← mkParams config #[grindExt.getState (← getEnv)]
  try
    let result ← Grind.main mvarId params
    let originName (o : Grind.Origin) : Name :=
      match o with
      | .decl d => d
      | .fvar .. | .local .. => const
      | _ => unreachable!
    let mut graph : Graph := { edges := {(const, {})} }
    let mut nodesWithParents : Std.HashSet Name := {}
    for diag in result.ematchDiags do
      let dst := originName diag.target.origin
      for source in diag.sources do
        graph := graph.addEdge (originName source.origin) dst
      if !diag.sources.isEmpty then
        nodesWithParents := nodesWithParents.insert dst
    for (node, _) in graph.edges.toArray do
      if !nodesWithParents.contains node then
        graph := graph.addEdge const node
    return graph
  catch _ =>
    return {}

def computeGraph (env : Environment) (targets : Array Name) : IO (Std.HashMap Name Graph) := do
  let options := Options.empty.insert `grind.ematch.diagnostics (.ofBool true)
  let ctx := { fileName := "<input>", fileMap := default, options }
  let mut graphs := {}
  for origin in targets do
    let (successors, _, _) ← MetaM.toIO (ctxCore := ctx) (sCore := { env := env }) do
      getSuccessors origin
    graphs := graphs.insert origin successors
  return graphs

def computeGraphs : CoreM (Std.HashMap Name Graph) := do
  let thms ← grindExt.getEMatchTheorems
  let mut targets := #[]
  for origin in thms.getOrigins do
    let .decl origin := origin | unreachable!
    targets := targets.push origin
  let chunkSize := 32
  let mut tasks := #[]
  let env ← getEnv
  for i in [0:targets.size:chunkSize] do
    let chunk := targets[i...(min (i + chunkSize) targets.size)].toArray
    tasks := tasks.push <| ← IO.asTask (computeGraph env chunk)
  tasks.foldlM (init := {}) (fun acc t => return acc.union (← IO.ofExcept t.get))

structure Export where
  graph : Graph
  origins : Array Name
  deriving ToJson


def countFilter := [filter| {.inModule `Init.Data.List.Find} ∧ ({.contains "findIdx"} ∧ ¬ {.contains "findIdx?"})]

def exportGraph : CoreM Unit := do
  let graphIndex ← computeGraphs
  let mut filterGraph : Graph := {}
  let mut origins := #[]
  for (name, graph) in graphIndex do
    if ← countFilter.eval name then
      origins := origins.push name
      filterGraph := filterGraph.merge graph
  let ex : Export := {
    graph := filterGraph
    origins := origins
  }
  IO.println (toJson ex).compress

#eval exportGraph
--#time #eval exportGraph
--#time #eval exportGraph

