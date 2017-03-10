set_option pp.all true
universe variables u v w

namespace X1

#print "\n1. ?U does not unify with anything"

inductive foo (A : Type u) (B : Type (v+1))
| mk : A → B → foo

#check @foo.{u v} -- : Type (max u (v+1))

end X1

namespace X2

#print "\n2. ?U unifies with a constant, no others above: done"

inductive bar (A : Sort 2) : Sort 2
| mk : A → bar

inductive foo
| mk : Type → bar foo → foo

#check @foo -- : Type 1

end X2

namespace X3
#print "\n3. ?U unifies with a constant, and one above: error"

inductive bar (A : Sort 2) : Sort 2
| mk : A → bar

inductive foo (A : Sort u)
| mk : A → bar foo → foo

end X3

namespace X4
#print "\n4. ?U unifies with a meta, but nesting recursor goes to Prop: error"

inductive bar (A : Sort u) : Sort u
| mk : A → bar

inductive foo
| mk : bar foo → foo

end X4

namespace X5
#print "\n5. ?U unifies with a meta: old approach, set level-param"

inductive bar (A : Sort u) : Sort (max u 1)
| mk : A → bar

inductive foo (A : Sort u)
| mk : A → bar foo → foo

#check @foo.{u} -- Sort u → Sort (max u 1)

end X5

namespace X6
#print "\n6. ?U unifies with a shifted meta, no others above: set level-param to be inverse of meta"

inductive bar (A : Sort (u + 3)) : Sort (u + 3)
| mk : A → bar

inductive foo (A : Sort u)
| mk : A → bar foo → foo

#check @foo.{u} -- Sort u → Sort (u+3)

end X6

namespace X7
#print "\n7. ?U unifies with a max: error"
inductive bar (A : Sort (max u v)) : Sort (max u v 7)
| mk : A → bar

inductive foo (A : Sort v)
| mk : A → bar foo → foo

end X7

namespace X8
#print "\n8. wrapping inductive returns element in different universe: error"
inductive bar (A : Sort u) : Sort (u + 1)
| mk : A → bar

inductive foo (A : Sort v)
| mk : A → bar foo → foo

end X8

namespace X9

#print "\n9. nesting with no other level params"

inductive bar (A : Sort u) : Sort (max u 1)
| mk : A → bar

inductive foo
| mk : bar foo → foo

#check @foo

end X9

namespace X10
#print "\n10. original 1343"

inductive foo (α : Sort (u+1)) : Sort (u+1)
| mk : α → foo

inductive bug
| mk   : foo bug → bug

#check @bug

end X10

namespace X11
#print "\n11. unifies with constant, result sort different: error"

inductive foo (α : Sort 2) : Sort 1
| mk : foo

inductive bug
| mk   : foo bug → bug

end X11

namespace X12
#print "\n12. multiple nestings"

inductive foo₁ (α : Sort u) : Sort (max u 1)
| mk : foo₁

inductive foo₂ (α : Type u) : Type u
| mk : foo₂

inductive foo₃ (α : Type (u+1)) : Type (u+1)
| mk : foo₃

inductive bug
| mk₁   : foo₁ bug → foo₂ bug → foo₃ bug → foo₃ (foo₂ (foo₁ bug)) → foo₁ (foo₂ (foo₃ bug)) → bug
| mk₂   : foo₁ bug → foo₂ bug → foo₃ bug → foo₃ (foo₂ (foo₁ bug)) → foo₁ (foo₂ (foo₃ bug)) → bug

#check @bug

end X12

namespace X13
#print "\n13. ?U indirectly assigned to a constant"

inductive foo (α β : Sort u) : Sort (max u 1)
| mk : foo

inductive bug
| mk₁   : foo bug (Type 3) → bug

#check @bug

end X13

namespace X14
#print "\n14. No resultant level and lps are used in intro rule: error"

inductive foo (α : Type u) : Type u
| mk : foo

inductive bug
| mk   : foo.{u} bug → bug

end X14
