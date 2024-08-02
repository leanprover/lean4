* Structural recursion can now be explicitly requested using
  ```
  termination_by structural x
  ```
  in analogy to the existing `termination_by x` syntax that causes well-founded recursion to be used.
  (#4542)

* The `termination_by?` syntax no longer forces the use of well-founded recursion, and when structural
  recursion is inferred, will print the result using the `termination_by` syntax.

* Mutual structural recursion is supported now. This supports both mutual recursion over a non-mutual
  data type, as well as recursion over mutual or nested data types:

  ```lean
  mutual
  def Even : Nat → Prop
    | 0 => True
    | n+1 => Odd n

  def Odd : Nat → Prop
    | 0 => False
    | n+1 => Even n
  end

  mutual
  inductive A
  | other : B → A
  | empty
  inductive B
  | other : A → B
  | empty
  end

  mutual
  def A.size : A → Nat
  | .other b => b.size + 1
  | .empty => 0

  def B.size : B → Nat
  | .other a => a.size + 1
  | .empty => 0
  end

  inductive Tree where | node : List Tree → Tree

  mutual
  def Tree.size : Tree → Nat
  | node ts => Tree.list_size ts

  def Tree.list_size : List Tree → Nat
  | [] => 0
  | t::ts => Tree.size t + Tree.list_size ts
  end
  ```

  Functional induction principles are generated for these functions as well (`A.size.induct`, `A.size.mutual_induct`).

  Nested structural recursion is still not supported.

  PRs #4639, #4715, #4642, #4656, #4684, #4715, #4728, #4575, #4731, #4658, #4734, #4738, #4718,
  #4733, #4787, #4788, #4789, #4807, #4772

* A bugfix in the structural recursion code may in some cases break existing code, when a parameter
  of the type of the recursive argument is bound behind indices of that type. This can usually be
  fixed by reordering the parameters of the function (PR #4672)
