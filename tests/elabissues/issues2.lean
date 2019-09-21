inductive Syntax
| atom : String → Syntax
| node : String → Array Syntax → Syntax

instance coe1 : HasCoe String Syntax := ⟨Syntax.atom⟩
instance coe2 {α} : HasCoe (List α) (Array α) := ⟨List.toArray⟩

def ex7 : Syntax :=
/-
We try to elaborate `["bla"]` with expected type `Array Syntax`.
The expected type is "discarded" since we fail to unify `Array Syntax =?= List ?A`
where `List ?A` is the resulting type for `List.cons` application before we process its children.
Remark: the elaborator does **not** try to use coercions here. Even if it tried, it would fail since
`List ?A` contains a meta-variable.
Then, we elaborate `["bla"]` without an expected type and produce a term of type `List String`.
Finally, we fail with a type mismatch between `List String` and `Array Nat`.
We can make it work by using:
```
instance coe3 {α β} [HasCoe α β] : HasCoe (List α) (Array β) := ⟨fun xs => (xs.map (fun x => (coe x : β))).toArray⟩
```
-/
Syntax.node "foo" ["bla"]

def ex8 : Syntax :=
Syntax.node "foo" (List.toArray ["boo"]) -- Works

def ex9 : Syntax :=
/-
We need the type of `["boo"]` to be able to apply `.toArray`.
So, we elaborate `["boo"]` first without expected type, and then
obtain `Array String`, and then a type mismatch between
`Array String` and `Array Syntax`.
We can make it work by using:
```
instance coe3 {α β} [HasCoe α β] : HasCoe (Array α) (Array β) := ⟨fun xs => (xs.map (fun x => (coe x : β)))⟩
```
But, the behavior is still confusing to users.
-/
Syntax.node "foo" ["boo"].toArray
