

unsafe def f (n : Nat) :=
let rec g (x : Nat) :=
if x > 0 then
  /- This example relies on the instance `coeId {α} (a : α) : CoeT α a α`,
     The type of `g` is not provided. Thus, the expected type is
     `?m x` since the elaborator assumes it may depend on `x`.
     Thus, the expected type for the addition is `?m x`.
     The type of `g (x-1)` is `?m (x-1)`. So, we have the unification
     problem
     ```
     ?m (x-1) =?= ?m x
     ```
     and it is rejected by the unifier. Thus, the elaborator inserts
     a coercion from `?m (x-1)` to `?m x` around `g (x-1)` which creates
     the pending TC problem:
     ```
     CoeT (?m (x-1)) (g (x-1)) (?m x)
     ```

     Remark: in principle, we could solve it using a heuristic: assume
     `?m` is a constant function.
     Later, when we elaborate the else branch `0`, we have that
     ```
     ?m x =?= Nat
     ```
     which is solved using `?m := (fun _ => Nat)`.
     Then, `@coeId Nat (g (x-1))` is used to synthesize
     ```
     CoeT (?m (x-1)) (g (x-1)) (?m x)
     ```
     which is
     ```
     CoeT Nat (g (x-1)) Nat
     ```
     after we apply the assignment `?m := (fun _ => Nat)`
     -/
  g (x-1) + n
else
  0;
g n

#eval f 10
