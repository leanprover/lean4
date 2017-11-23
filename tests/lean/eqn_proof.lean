universes u

inductive node (α : Type u)
| leaf : node
| red_node : node → α → node → node
| black_node : node → α → node → node

namespace node
variable {α : Type u}

def balance : node α → α → node α → node α
| (red_node (red_node a x b) y c) k d := red_node (black_node a x b) y (black_node c k d)
| (red_node a x (red_node b y c)) k d := red_node (black_node a x b) y (black_node c k d)
| l k r                               := black_node l k r

#print balance._main.equations._eqn_1

end node
