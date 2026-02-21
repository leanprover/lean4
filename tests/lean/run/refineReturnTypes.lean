-- Tests for the refineReturnTypes pass

inductive MyTree where
  | leaf : MyTree
  | node : MyTree → MyTree → MyTree

-- A function that always allocates a node constructor (object): tobj → obj
set_option trace.Compiler.refineReturnTypes true in
/--
trace: [Compiler.refineReturnTypes] alwaysNode: tobj → obj
[Compiler.refineReturnTypes] size: 1
    def alwaysNode l r : obj :=
      let _x.1 := ctor_1[MyTree.node]  l r;
      return _x.1
-/
#guard_msgs (whitespace := lax) in
@[noinline] def alwaysNode (l r : MyTree) : MyTree :=
  MyTree.node l r

-- A function that always returns a leaf (tagged scalar constructor): tobj → tagged
set_option trace.Compiler.refineReturnTypes true in
/--
trace: [Compiler.refineReturnTypes] alwaysLeaf: tobj → tagged
[Compiler.refineReturnTypes] size: 1
    def alwaysLeaf : tagged :=
      let _x.1 := ctor_0[MyTree.leaf] ;
      return _x.1
-/
#guard_msgs (whitespace := lax) in
@[noinline] def alwaysLeaf : MyTree :=
  MyTree.leaf

-- A function that returns both leaf (tagged) and node (object) — no refinement possible.
-- The trace should show the decl as still having tobj return type.
set_option trace.Compiler.refineReturnTypes true in
/--
trace: [Compiler.refineReturnTypes] size: 5
    def eitherKind b t : tobj :=
      cases b : tobj
      | Bool.false =>
        let _x.1 := ctor_1[MyTree.node]  t t;
        return _x.1
      | Bool.true =>
        let _x.2 := ctor_0[MyTree.leaf] ;
        return _x.2
[Compiler.refineReturnTypes] size: 2
    def eitherKind._boxed b t : tobj :=
      let b.boxed := unbox b;
      let res := eitherKind b.boxed t;
      return res
-/
#guard_msgs (whitespace := lax) in
@[noinline] def eitherKind (b : Bool) (t : MyTree) : MyTree :=
  if b then MyTree.leaf else MyTree.node t t

-- Verify runtime behavior
/-- info: MyTree.node (MyTree.leaf) (MyTree.leaf) -/
#guard_msgs in
#eval alwaysNode MyTree.leaf MyTree.leaf

/-- info: MyTree.leaf -/
#guard_msgs in
#eval alwaysLeaf

/-- info: MyTree.leaf -/
#guard_msgs in
#eval eitherKind true MyTree.leaf

/-- info: MyTree.node (MyTree.leaf) (MyTree.leaf) -/
#guard_msgs in
#eval eitherKind false MyTree.leaf
