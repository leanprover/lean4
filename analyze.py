import itertools
import json

import networkx as nx
from pyvis.network import Network

# Nodes whose name contains any of these substrings (and their incident edges)
# are excluded from the graph.
BLOCKLIST = ["sizeOf_spec"]


def is_blocked(name):
    return any(pattern in name for pattern in BLOCKLIST)


# Mass of a core node; heavier nodes act as gravitational anchors that the
# lighter periphery arranges itself around. 1 is the vis-network default.
CORE_MASS = 10


with open("graph.json", "r") as graph_json:
    data = json.load(graph_json)

graph = data["graph"]
origins = set(data["origins"])

# Each entry is [source, [[dest, weight], ...]].
G = nx.DiGraph()
for source, destinations in graph:
    if is_blocked(source):
        continue
    G.add_node(source)
    for destination, weight in destinations:
        if is_blocked(destination):
            continue
        G.add_edge(source, destination, weight=weight, value=weight)

# Highlight origin nodes in orange.
for node in G.nodes:
    if node in origins:
        G.nodes[node]["color"] = "orange"

print(f"nodes: {G.number_of_nodes()}, edges: {G.number_of_edges()}")

# Connected-component analysis on the undirected view of the graph.
components = sorted(nx.connected_components(G.to_undirected()), key=len, reverse=True)
print(f"connected components: {len(components)}")
for i, component in enumerate(components):
    component_origins = [node for node in component if node in origins]
    print(f"  component {i}: {len(component)} nodes, {len(component_origins)} origins")

net = Network(
    height="900px",
    width="100%",
    directed=True,
    select_menu=True,  # dropdown to search/select a node by name
    filter_menu=True,  # panel to filter nodes/edges by property
    cdn_resources="in_line",  # self-contained HTML, no external fetches
)
net.from_nx(G)

# Within each component, add invisible springs between origin nodes so related
# origins cluster together. A hidden vis-network edge is not drawn but still
# participates in the physics simulation.
for component in components:
    component_origins = [node for node in component if node in origins]
    for a, b in itertools.combinations(component_origins, 2):
        net.add_edge(a, b, hidden=True, physics=True)

# Force-directed (spring) layout computed live in the browser.
net.barnes_hut(
    gravity=-8000,
    central_gravity=0.3,
    spring_length=120,
    spring_strength=0.04,
    damping=0.09,
)
net.show_buttons(filter_=["physics"])

net.write_html("graph.html", notebook=False)
print("saved graph.html")
