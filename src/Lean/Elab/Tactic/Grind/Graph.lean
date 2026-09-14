/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Elab.Command
import Init.Grind.Graph
import Lean.Elab.Tactic.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Std.Http

namespace Lean.Elab.Tactic.Grind

open Command Meta Lean.Meta.Grind

structure Graph where
  edges : Std.HashMap Name (Std.HashMap Name Nat) := {}

namespace Graph

instance : ToJson Graph where
  toJson g := toJson <| g.edges.toArray |>.map fun (k, v) => (k, v.toArray)

def addEdge (g : Graph) (src dst : Name) : Graph :=
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

def undirectedComponents (g : Graph) : Array (Std.HashSet Name) := Id.run do
  let mut undirected := g
  for (src, dsts) in g.edges do
    for (dst, _) in dsts do
      undirected := undirected.addEdge dst src

  let mut seen : Std.HashSet Name := {}
  let mut worklist := g.edges.keysArray
  let mut components := #[]
  while h : worklist.size ≠ 0 do
    let node := worklist.back
    worklist := worklist.pop
    if seen.contains node then continue
    let component := collect undirected node
    components := components.push component
    seen := seen.union component
  return components
where
  collect (g : Graph) (src : Name) : Std.HashSet Name := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut worklist := #[src]
    let mut component := {src}
    while h : worklist.size ≠ 0 do
      let node := worklist.back
      worklist := worklist.pop
      if seen.contains node then continue
      let edges := g.edges[node]!
      for (dst, _) in edges do
        component := component.insert dst
        unless seen.contains dst do
          worklist := worklist.push dst
      seen := seen.insert node
    return component

/--
Standalone HTML page rendering a `Graph` with [vis-network](https://visjs.github.io/vis-network/),
loaded from cdnjs. `graphJson` is the JSON of the graph, i.e. an array of
`[source, [[target, weight], ...]]` entries, `groupsJson` an array of groups of names. All of the
grouped names are drawn in orange, and the members of a group additionally attract each other.
-/
def htmlTemplate (graphJson groupsJson : String) : String := r#"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>grind graph</title>
<link
  rel="stylesheet"
  href="https://cdnjs.cloudflare.com/ajax/libs/vis-network/10.1.1/dist/dist/vis-network.min.css"
  integrity="sha512-WgxfT5LWjfszlPHXRmBWHkV2eceiWTOBvrKCNbdgDYTHrT2AeLCGbF4sZlZw3UMN3WtL0tGUoIAKsu8mllg/XA=="
  crossorigin="anonymous"
  referrerpolicy="no-referrer">
<script
  src="https://cdnjs.cloudflare.com/ajax/libs/vis-network/10.1.1/standalone/umd/vis-network.min.js"
  integrity="sha512-UE4GUzz6a74ilrjSoMSOY0aVxhRPzFWfq0N//oFJG6eGJD4wVADzsJGWQWNiM55yy3tiniGwlnNeLLsTe2oAnw=="
  crossorigin="anonymous"
  referrerpolicy="no-referrer"></script>
<style>
  /* vis-network takes the canvas size from its container, so that height must not depend on the
     canvas in turn: a content-derived height (a `flex: 1` item, say) makes the two grow each other
     without bound. The physics panel is long enough that it needs a scroll region of its own. */
  body { margin: 0; }
  #graph { height: 65vh; }
  #physics { box-sizing: border-box; max-height: 35vh; overflow-y: auto; border-top: 1px solid #ccc; }
</style>
</head>
<body>
<div id="graph"></div>
<div id="physics"></div>
<script>
'use strict';

// Array of [source, [[target, weight], ...]] entries.
const ADJACENCY = "# ++ graphJson ++ r#";
const GROUPS = "# ++ groupsJson ++ r#";
const HIGHLIGHTED = new Set(GROUPS.flat());

// Nodes only occurring as targets are not keys of the adjacency, so collect both endpoints.
const degree = new Map();
const edges = [];
for (const [source, targets] of ADJACENCY) {
  for (const [target, weight] of targets) {
    degree.set(source, (degree.get(source) || 0) + 1);
    degree.set(target, (degree.get(target) || 0) + 1);
    edges.push({ from: source, to: target, value: weight });
  }
}

// A hidden edge is not drawn but still takes part in the simulation, so a clique of them pulls a
// group together. `length` is the spring's rest length, the only per-edge physics knob vis-network
// has; the force it exerts also scales with the global spring constant in the panel below.
const CLUSTER_LENGTH = 100;
for (const group of GROUPS) {
  const members = group.filter((id) => degree.has(id));
  for (let i = 0; i < members.length; i++) {
    for (let j = i + 1; j < members.length; j++) {
      edges.push({ from: members[i], to: members[j], hidden: true, length: CLUSTER_LENGTH });
    }
  }
}

const nodes = [...degree].map(([id, value]) => {
  const node = { id, label: id, value };
  if (HIGHLIGHTED.has(id)) node.color = 'orange';
  return node;
});

// `value` opts nodes and edges into vis-network's default scaling, sizing them by degree and by
// how often the instantiation was seen.
new vis.Network(
  document.getElementById('graph'),
  { nodes: new vis.DataSet(nodes), edges: new vis.DataSet(edges) },
  {
    nodes: { shape: 'dot' },
    edges: { arrows: 'to' },
    configure: {
      enabled: true,
      filter: 'physics',
      container: document.getElementById('physics'),
      showButton: false
    }
  });
</script>
</body>
</html>
"#

def toHtml (g : Graph) (groups : Array (Array Name)) : String :=
  htmlTemplate (toJson g).compress (toJson groups).compress

end Graph

def analyzeTheorem (declName : Name) (params : Grind.Params) (graph : Graph) : MetaM Graph := do
  let info ← getConstInfo declName
  let mvarId ← forallTelescope info.type fun _ type => do
    withLocalDeclD `h type fun _ => do
      return (← mkFreshExprMVar (mkConst ``False)).mvarId!
  let result ← withOptions (fun opts => opts.setBool `grind.ematch.diagnostics true) do
    Grind.main mvarId params
  let originName (o : Grind.Origin) : Name :=
    match o with
    | .decl d => d
    | .fvar .. | .local .. => declName
    | _ => unreachable!
  let mut nodesWithParents : Std.HashSet Name := {}
  let mut sources : Std.HashSet Name := {}
  let mut graph := graph
  for diag in result.ematchDiags do
    let dst := originName diag.target.origin
    for source in diag.sources do
      let src := originName source.origin
      sources := sources.insert src
      graph := graph.addEdge src dst
    if !diag.sources.isEmpty then
      nodesWithParents := nodesWithParents.insert dst
  for node in sources do
    if !nodesWithParents.contains node then
      graph := graph.addEdge declName node
  return graph

def analyzeDeclNames (declNames : Array Name) (params : Grind.Params) : MetaM String := do
  let mut graph := {}
  let declNames := .ofArray declNames
  for declName in declNames do
    graph ← analyzeTheorem declName params graph
  let sourceComponents := graph.undirectedComponents |>.map (·.inter declNames |>.toArray)
  let html := graph.toHtml sourceComponents
  return html

open _root_.Std Async Http in
def serve (html : String) : MetaM Unit := Async.block do
  let done ← IO.Promise.new
  let handler := Server.Handler.ofFn fun _req => do
    let r ← Response.ok
      |>.header! "Access-Control-Allow-Origin" "*"
      |>.html html
    done.resolve ()
    return r
  let addr : Net.SocketAddress := .v4 (.mk (.ofParts 127 0 0 1) 0)
  let server ← Server.serve addr handler
  let some localAddr := server.localAddr
    | throw <| IO.userError "#grind_graph: server did not report a bound address"


@[builtin_command_elab Lean.Grind.grindGraph]
def elabGrindGraph : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#grind_graph $[$items:configItem]* $[module%$m?]? $ids:ident* $[with $filter?:str]?
        $[> $file?:str]?) := stx
    | throwUnsupportedSyntax
  let config ← elabConfigItems {} items
  let params ← mkDefaultParams config
  let mut declNames := #[]
  if m?.isSome then
    let env ← getEnv
    let eMatchThms ← grindExt.getEMatchTheorems
    for id in ids do
      let moduleName := id.getId
      let some moduleIdx := env.getModuleIdx? moduleName
        | throwErrorAt id m!"{moduleName} is not imported"
      for const in env.header.moduleData[moduleIdx]!.constants do
        if eMatchThms.contains (.decl const.name) then
          declNames := declNames.push const.name
  else
    declNames ← ids.mapM (fun id => realizeGlobalConstNoOverloadWithInfo id)
  if let some filter := filter? then
    let filter := filter.getString
    declNames := declNames.filter (·.toString.contains filter)
  let html ← analyzeDeclNames declNames params
  if let some file := file? then
    let path : System.FilePath := file.getString
    IO.FS.writeFile path html
    logInfo m!"wrote {path}"
  else
    IO.println html

end Lean.Elab.Tactic.Grind
