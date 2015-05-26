notation `C⁽` := nat
definition foo (c : C⁽) := nat.rec_on c _ _

notation `α⁽` := nat
definition foo (c : α⁽) := nat.rec_on c _ _

notation `_⁽` := nat
definition foo (c : _⁽) := nat.rec_on c _ _

notation `C.⁽` := nat
definition foo (c : C.⁽) := nat.rec_on c _ _

notation `C⁽C⁽` := nat
definition foo (c : C⁽C⁽) := nat.rec_on c _ _
