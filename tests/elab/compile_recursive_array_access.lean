/-!
This test asserts that the compiler is able to handle compilation of functions that recurse through
nested arrays in a way that does not unnecessarily remove borrow annotations.
-/


inductive NAryTree where
  | tip (x : String)
  | node (ys : Array NAryTree)
  deriving Inhabited

/--
trace: [Compiler.explicitRc] size: 21
    def followPath @&tree @&path : obj :=
      cases tree : obj
      | NAryTree.tip =>
        cases path : obj
        | List.nil =>
          let x.1 := oproj[0] tree;
          inc[ref] x.1;
          return x.1
        | _ =>
          let _x.2 := instInhabitedNAryTree.default._closed_0;
          inc[persistent][ref] _x.2;
          return _x.2
      | NAryTree.node =>
        cases path : obj
        | List.cons =>
          let ys.3 := oproj[0] tree;
          let head.4 := oproj[0] path;
          let tail.5 := oproj[1] path;
          let _x.6 := instInhabitedNAryTree.default;
          let _x.7 := Array.get!InternalBorrowed ◾ _x.6 ys.3 head.4;
          let _x.8 := followPath _x.7 tail.5;
          return _x.8
        | _ =>
          let _x.9 := instInhabitedNAryTree.default._closed_0;
          inc[persistent][ref] _x.9;
          return _x.9
[Compiler.explicitRc] size: 3
    def followPath._boxed tree path : obj :=
      let res := followPath tree path;
      dec path;
      dec[ref] tree;
      return res
-/
#guard_msgs in
set_option trace.Compiler.explicitRc true in
def followPath (tree : NAryTree) (path : List Nat) : String :=
  match tree, path with
  | .tip x, [] => x
  | .node ys, idx :: path => followPath ys[idx]! path
  | _, _ => default
